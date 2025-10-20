package ca.uwaterloo.flix.language.phase

import ca.uwaterloo.flix.api.Flix
import ca.uwaterloo.flix.language.ast.ReducedAst.*
import ca.uwaterloo.flix.language.ast.ReducedAst.Expr.*
import ca.uwaterloo.flix.language.ast.SimpleType.erase
import ca.uwaterloo.flix.language.ast.{AtomicOp, Purity, ReducedAst, SimpleType, SourceLocation, Symbol, Type, TypeConstructor}
import ca.uwaterloo.flix.language.dbg.AstPrinter.DebugReducedAst
import ca.uwaterloo.flix.util.collection.ListOps
import ca.uwaterloo.flix.util.{InternalCompilerException, ParOps}

import java.util.concurrent.ConcurrentHashMap
import java.util.function.BiConsumer
import scala.annotation.unused
import scala.collection.mutable

/**
  * Erase types and introduce corresponding casting
  *
  * Protocol is that casting should happen as soon as possible, not lazily.
  * This means that expressions should cast their output but assume correct
  * input types.
  *
  *   - Ref
  *     - component type erasure
  *   - Tuple
  *     - component type erasure
  *     - index casting
  *   - Record
  *     - component type erasure
  *     - select casting
  *   - Lazy
  *     - component type erasure
  *     - force casting
  *   - Function
  *     - result type boxing, this includes return types of defs and their applications
  *     - function call return value casting
  *   - Enums and Structs
  *     - Declarations are erased and specialized.
  */
object Eraser {

  def run(root: Root)(implicit flix: Flix): Root = flix.phase("Eraser") {
    assert(root.monoEnums.isEmpty)
    assert(root.monoStructs.isEmpty)

    implicit val r: Root = root
    implicit val ctx: SharedContext = new SharedContext()

    val newDefs = ParOps.parMapValues(root.defs)(visitDef)
    val newEnums = specializeEnums(root, ctx.getEnumSpecializations)
    val newStructs = specializeStructs(root, ctx.getStructSpecializations)
    val newEffects = ParOps.parMapValues(root.effects)(visitEffect)
    root.copy(defs = newDefs, enums = Map.empty, monoEnums = newEnums, structs = Map.empty, monoStructs = newStructs, effects = newEffects)
  }

  private def specializeEnums(root: Root, enums: Iterable[(Symbol.EnumSym, List[SimpleType], Symbol.EnumSym)]): Map[Symbol.EnumSym, ReducedAst.MonoEnum] =
    enums.map { case (sym, targs, newSym) => newSym -> specializeEnum(newSym, root.enums(sym), targs) }.toMap

  private def specializeEnum(newSym: Symbol.EnumSym, enm: ReducedAst.Enum, targs: List[SimpleType]): ReducedAst.MonoEnum = {
    val subst = ListOps.zip(enm.tparams.map(_.sym), targs).toMap
    val cases = enm.cases.map { case (sym, caze) => sym -> specializeCase(newSym, subst, caze) }
    ReducedAst.MonoEnum(enm.ann, enm.mod, newSym, cases, enm.loc)
  }

  private def specializeCase(newSym: Symbol.EnumSym, subst: Map[Symbol.KindedTypeVarSym, SimpleType], caze: ReducedAst.Case): ReducedAst.MonoCase = {
    val sym = new Symbol.CaseSym(newSym, caze.sym.name, caze.sym.loc)
    val tpes = caze.tpes.map(instantiateType(subst, _))
    ReducedAst.MonoCase(sym, tpes, caze.loc)
  }

  private def specializeStructs(root: Root, structs: Iterable[(Symbol.StructSym, List[SimpleType], Symbol.StructSym)]): Map[Symbol.StructSym, ReducedAst.MonoStruct] = {
    structs.map { case (sym, targs, newSym) => newSym -> specializeStruct(newSym, root.structs(sym), targs) }.toMap
  }

  private def specializeStruct(newSym: Symbol.StructSym, struct: ReducedAst.Struct, targs: List[SimpleType]): ReducedAst.MonoStruct = {
    val subst = ListOps.zip(struct.tparams.map(_.sym), targs).toMap
    val fields = struct.fields.map(specializeField(newSym, subst, _))
    ReducedAst.MonoStruct(struct.ann, struct.mod, newSym, fields, struct.loc)
  }

  private def specializeField(newSym: Symbol.StructSym, subst: Map[Symbol.KindedTypeVarSym, SimpleType], field: ReducedAst.StructField): ReducedAst.MonoStructField = {
    val sym = new Symbol.StructFieldSym(newSym, field.sym.name, field.sym.loc)
    val tpe = instantiateType(subst, field.tpe)
    ReducedAst.MonoStructField(sym, tpe, field.loc)
  }

  /**
    * Instantiates `tpe` given the variable map `subst`.
    *
    * Examples:
    *   - `instantiateType([x -> Int32], x) = Int32`
    *   - `instantiateType(_, Int32) = Int32`
    *   - `instantiateType(_, Object) = Object`
    *   - `instantiateType([x -> String], x) = throw InternalCompilerException`
    *   - `instantiateType([x -> Int32], y) = throw InternalCompilerException`
    *   - `instantiateType(_, Option[Int32]) =  throw InternalCompilerException`
    *
    * @param subst Decides types for variables, must only contain erased types.
    * @param tpe   The type to instantiate, must be a polymorphic erased type
    *              (either [[Type.Var]], a primitive type, or `java.lang.Object`)
    */
  private def instantiateType(subst: Map[Symbol.KindedTypeVarSym, SimpleType], tpe: Type): SimpleType = tpe match {
    case Type.Var(sym, _) => subst(sym)
    case Type.Cst(tc, _) => tc match {
      case TypeConstructor.Bool => SimpleType.Bool
      case TypeConstructor.Char => SimpleType.Char
      case TypeConstructor.Float32 => SimpleType.Float32
      case TypeConstructor.Float64 => SimpleType.Float64
      case TypeConstructor.Int8 => SimpleType.Int8
      case TypeConstructor.Int16 => SimpleType.Int16
      case TypeConstructor.Int32 => SimpleType.Int32
      case TypeConstructor.Int64 => SimpleType.Int64
      case TypeConstructor.Native(clazz) if clazz == classOf[Object] => SimpleType.Object
      case _ => throw InternalCompilerException(s"Unexpected type: '$tpe'", tpe.loc)
    }
    case Type.Apply(_, _, _) => throw InternalCompilerException(s"Unexpected type: '$tpe'", tpe.loc)
    case Type.Alias(_, _, _, _) => throw InternalCompilerException(s"Unexpected type: '$tpe'", tpe.loc)
    case Type.AssocType(_, _, _, _) => throw InternalCompilerException(s"Unexpected type: '$tpe'", tpe.loc)
    case Type.JvmToType(_, _) => throw InternalCompilerException(s"Unexpected type: '$tpe'", tpe.loc)
    case Type.JvmToEff(_, _) => throw InternalCompilerException(s"Unexpected type: '$tpe'", tpe.loc)
    case Type.UnresolvedJvmType(_, _) => throw InternalCompilerException(s"Unexpected type: '$tpe'", tpe.loc)
  }

  private def visitDef(defn: Def)(implicit ctx: SharedContext, root: Root, flix: Flix): Def = defn match {
    case Def(ann, mod, sym, cparams, fparams, lparams, pcPoints, exp, tpe, originalTpe, loc) =>
      val eNew = visitExp(exp)
      val e = Expr.ApplyAtomic(AtomicOp.Box, List(eNew), box(tpe), exp.purity, loc)
      Def(ann, mod, sym, cparams.map(visitParam), fparams.map(visitParam), lparams.map(visitLocalParam), pcPoints, e, box(tpe), UnboxedType(erase(originalTpe.tpe)), loc)
  }

  private def visitParam(fp: FormalParam): FormalParam = fp match {
    case FormalParam(sym, tpe) =>
      FormalParam(sym, visitType(tpe))
  }

  private def visitLocalParam(p: LocalParam): LocalParam = p match {
    case LocalParam(sym, tpe) =>
      LocalParam(sym, visitType(tpe))
  }

  private def visitBranch(branch: (Symbol.LabelSym, Expr))(implicit ctx: SharedContext, root: Root, flix: Flix): (Symbol.LabelSym, Expr) = branch match {
    case (sym, exp) =>
      (sym, visitExp(exp))
  }

  private def visitCatchRule(rule: CatchRule)(implicit ctx: SharedContext, root: Root, flix: Flix): CatchRule = rule match {
    case CatchRule(sym, clazz, exp) =>
      CatchRule(sym, clazz, visitExp(exp))
  }

  private def visitHandlerRule(rule: HandlerRule)(implicit ctx: SharedContext, root: Root, flix: Flix): HandlerRule = rule match {
    case HandlerRule(op, fparams, exp) =>
      HandlerRule(op, fparams.map(visitParam), visitExp(exp))
  }

  private def visitJvmMethod(method: JvmMethod)(implicit ctx: SharedContext, root: Root, flix: Flix): JvmMethod = method match {
    case JvmMethod(ident, fparams, clo, retTpe, purity, loc) =>
      // return type is not erased to maintain class signatures
      JvmMethod(ident, fparams.map(visitParam), visitExp(clo), visitType(retTpe), purity, loc)
  }

  private def visitExp(exp0: Expr)(implicit ctx: SharedContext, root: Root, flix: Flix): Expr = exp0 match {
    case Cst(cst, loc) =>
      Cst(cst, loc)
    case Var(sym, tpe, loc) =>
      Var(sym, visitType(tpe), loc)
    case ApplyAtomic(op, exps, tpe, purity, loc) =>
      val es = exps.map(visitExp)
      val t = visitType(tpe)
      op match {
        case AtomicOp.Closure(_) => ApplyAtomic(op, es, t, purity, loc)
        case AtomicOp.Unary(_) => ApplyAtomic(op, es, t, purity, loc)
        case AtomicOp.Binary(_) => ApplyAtomic(op, es, t, purity, loc)
        case AtomicOp.Is(sym0) =>
          val List(e) = es
          val newEnumSym = e.tpe.asInstanceOf[SimpleType.MonoEnum].sym
          val sym = new Symbol.CaseSym(newEnumSym, sym0.name, sym0.loc)
          ApplyAtomic(AtomicOp.Is(sym), es, t, purity, loc)
        case AtomicOp.Tag(sym0) =>
          val newEnumSym = t.asInstanceOf[SimpleType.MonoEnum].sym
          val sym = new Symbol.CaseSym(newEnumSym, sym0.name, sym0.loc)
          ApplyAtomic(AtomicOp.Tag(sym), es, t, purity, loc)
        case AtomicOp.Untag(sym0, idx) =>
          val List(e) = es
          val newEnumSym = e.tpe.asInstanceOf[SimpleType.MonoEnum].sym
          val sym = new Symbol.CaseSym(newEnumSym, sym0.name, sym0.loc)
          ApplyAtomic(AtomicOp.Untag(sym, idx), es, t, purity, loc)
        case AtomicOp.Index(_) =>
          castExp(ApplyAtomic(op, es, erase(tpe), purity, loc), t, purity, loc)
        case AtomicOp.Tuple => ApplyAtomic(op, es, t, purity, loc)
        case AtomicOp.RecordSelect(_) =>
          castExp(ApplyAtomic(op, es, erase(tpe), purity, loc), t, purity, loc)
        case AtomicOp.RecordExtend(_) => ApplyAtomic(op, es, t, purity, loc)
        case AtomicOp.RecordRestrict(_) => ApplyAtomic(op, es, t, purity, loc)
        case AtomicOp.ExtIs(_) => ApplyAtomic(op, es, t, purity, loc)
        case AtomicOp.ExtTag(_) => ApplyAtomic(op, es, t, purity, loc)
        case AtomicOp.ExtUntag(_, _) => ApplyAtomic(op, es, t, purity, loc)
        case AtomicOp.ArrayLit => ApplyAtomic(op, es, t, purity, loc)
        case AtomicOp.ArrayNew => ApplyAtomic(op, es, t, purity, loc)
        case AtomicOp.ArrayLoad => ApplyAtomic(op, es, t, purity, loc)
        case AtomicOp.ArrayStore => ApplyAtomic(op, es, t, purity, loc)
        case AtomicOp.ArrayLength => ApplyAtomic(op, es, t, purity, loc)
        case AtomicOp.StructNew(_, fields0) =>
          val sym = t.asInstanceOf[SimpleType.MonoStruct].sym
          val fields = fields0.map(fieldSym => new Symbol.StructFieldSym(sym, fieldSym.name, fieldSym.loc))
          ApplyAtomic(AtomicOp.StructNew(sym, fields), es, t, purity, loc)
        case AtomicOp.StructGet(sym0) =>
          ???
          castExp(ApplyAtomic(op, es, erase(tpe), purity, loc), t, purity, loc)
        case AtomicOp.StructPut(_) => ApplyAtomic(op, es, t, purity, loc)
        case AtomicOp.InstanceOf(_) => ApplyAtomic(op, es, t, purity, loc)
        case AtomicOp.Cast => ApplyAtomic(op, es, t, purity, loc)
        case AtomicOp.Unbox => ApplyAtomic(op, es, t, purity, loc)
        case AtomicOp.Box => ApplyAtomic(op, es, t, purity, loc)
        case AtomicOp.InvokeConstructor(_) => ApplyAtomic(op, es, t, purity, loc)
        case AtomicOp.InvokeMethod(_) => ApplyAtomic(op, es, t, purity, loc)
        case AtomicOp.InvokeStaticMethod(_) => ApplyAtomic(op, es, t, purity, loc)
        case AtomicOp.GetField(_) => ApplyAtomic(op, es, t, purity, loc)
        case AtomicOp.PutField(_) => ApplyAtomic(op, es, t, purity, loc)
        case AtomicOp.GetStaticField(_) => ApplyAtomic(op, es, t, purity, loc)
        case AtomicOp.PutStaticField(_) => ApplyAtomic(op, es, t, purity, loc)
        case AtomicOp.Throw => ApplyAtomic(op, es, t, purity, loc)
        case AtomicOp.Spawn => ApplyAtomic(op, es, t, purity, loc)
        case AtomicOp.Lazy => ApplyAtomic(op, es, t, purity, loc)
        case AtomicOp.Force =>
          castExp(ApplyAtomic(op, es, erase(tpe), purity, loc), t, purity, loc)
        case AtomicOp.HoleError(_) => ApplyAtomic(op, es, t, purity, loc)
        case AtomicOp.MatchError => ApplyAtomic(op, es, t, purity, loc)
        case AtomicOp.CastError(_, _) => ApplyAtomic(op, es, t, purity, loc)
      }

    case ApplyClo(exp1, exp2, ct, tpe, purity, loc) =>
      val ac = ApplyClo(visitExp(exp1), visitExp(exp2), ct, box(tpe), purity, loc)
      castExp(unboxExp(ac, erase(tpe), purity, loc), visitType(tpe), purity, loc)
    case ApplyDef(sym, exps, ct, tpe, purity, loc) =>
      val ad = ApplyDef(sym, exps.map(visitExp), ct, box(tpe), purity, loc)
      castExp(unboxExp(ad, erase(tpe), purity, loc), visitType(tpe), purity, loc)
    case ApplyOp(sym, exps, tpe, purity, loc) =>
      ApplyOp(sym, exps.map(visitExp), visitType(tpe), purity, loc)
    case ApplySelfTail(sym, actuals, tpe, purity, loc) =>
      ApplySelfTail(sym, actuals.map(visitExp), visitType(tpe), purity, loc)
    case IfThenElse(exp1, exp2, exp3, tpe, purity, loc) =>
      IfThenElse(visitExp(exp1), visitExp(exp2), visitExp(exp3), visitType(tpe), purity, loc)
    case Branch(exp, branches, tpe, purity, loc) =>
      Branch(visitExp(exp), branches.map(visitBranch), visitType(tpe), purity, loc)
    case JumpTo(sym, tpe, purity, loc) =>
      JumpTo(sym, visitType(tpe), purity, loc)
    case Let(sym, exp1, exp2, loc) =>
      Let(sym, visitExp(exp1), visitExp(exp2), loc)
    case Stmt(exp1, exp2, loc) =>
      Stmt(visitExp(exp1), visitExp(exp2), loc)
    case Region(sym, exp, tpe, purity, loc) =>
      Region(sym, visitExp(exp), visitType(tpe), purity, loc)
    case TryCatch(exp, rules, tpe, purity, loc) =>
      TryCatch(visitExp(exp), rules.map(visitCatchRule), visitType(tpe), purity, loc)
    case RunWith(exp, effUse, rules, ct, tpe, purity, loc) =>
      val tw = RunWith(visitExp(exp), effUse, rules.map(visitHandlerRule), ct, box(tpe), purity, loc)
      castExp(unboxExp(tw, erase(tpe), purity, loc), visitType(tpe), purity, loc)
    case NewObject(name, clazz, tpe, purity, methods, loc) =>
      NewObject(name, clazz, visitType(tpe), purity, methods.map(visitJvmMethod), loc)
  }

  private def castExp(exp: Expr, t: SimpleType, purity: Purity, loc: SourceLocation): Expr = {
    Expr.ApplyAtomic(AtomicOp.Cast, List(exp), t, purity, loc.asSynthetic)
  }

  private def unboxExp(exp: Expr, t: SimpleType, purity: Purity, loc: SourceLocation): Expr = {
    Expr.ApplyAtomic(AtomicOp.Unbox, List(exp), t, purity, loc.asSynthetic)
  }

  private def visitEffect(eff: Effect): Effect = eff match {
    case Effect(ann, mod, sym, ops, loc) =>
      Effect(ann, mod, sym, ops.map(visitOp), loc)
  }

  private def visitOp(op: Op): Op = op match {
    case Op(sym, ann, mod, fparams, tpe, purity, loc) =>
      Op(sym, ann, mod, fparams.map(visitParam), erase(tpe), purity, loc)
  }

  private def visitType(tpe0: SimpleType): SimpleType = {
    import SimpleType.*
    tpe0 match {
      case Void => Void
      case AnyType => AnyType
      case Unit => Unit
      case Bool => Bool
      case Char => Char
      case Float32 => Float32
      case Float64 => Float64
      case BigDecimal => BigDecimal
      case Int8 => Int8
      case Int16 => Int16
      case Int32 => Int32
      case Int64 => Int64
      case BigInt => BigInt
      case String => String
      case Regex => Regex
      case Region => Region
      case Null => Null
      case Array(tpe) => SimpleType.mkArray(visitType(tpe))
      case Lazy(tpe) => Lazy(erase(tpe))
      case Tuple(elms) => SimpleType.mkTuple(elms.map(erase))
      case SimpleType.Enum(sym, targs) => SimpleType.mkEnum(sym, targs.map(erase))
      case SimpleType.Struct(sym, tparams) => SimpleType.Struct(sym, tparams.map(erase))
      case Arrow(args, result) => SimpleType.mkArrow(args.map(visitType), box(result))
      case RecordEmpty => RecordEmpty
      case RecordExtend(label, value, rest) => RecordExtend(label, erase(value), visitType(rest))
      case ExtensibleExtend(cons, tpes, rest) => ExtensibleExtend(cons, tpes.map(erase), visitType(rest))
      case ExtensibleEmpty => ExtensibleEmpty
      case Native(clazz) => Native(clazz)
      case MonoEnum(_) => throw InternalCompilerException(s"Unexpected type '$tpe0'", SourceLocation.Unknown)
      case MonoStruct(_) => throw InternalCompilerException(s"Unexpected type '$tpe0'", SourceLocation.Unknown)
    }
  }

  private def box(@unused tpe: SimpleType): SimpleType = SimpleType.Object

  private def unifyTypes(targs: List[SimpleType], tparams: List[Type]): Map[Symbol.KindedTypeVarSym, SimpleType] = {
    ???
  }

  private class SharedContext() {

    private val enumSpecializations: ConcurrentHashMap[(Symbol.EnumSym, List[SimpleType]), Symbol.EnumSym] = new ConcurrentHashMap()

    private val structSpecializations: ConcurrentHashMap[(Symbol.StructSym, List[SimpleType]), Symbol.StructSym] = new ConcurrentHashMap()

    def getEnumSpecializations: Iterable[(Symbol.EnumSym, List[SimpleType], Symbol.EnumSym)] =
      toArray(enumSpecializations)

    def getStructSpecializations: Iterable[(Symbol.StructSym, List[SimpleType], Symbol.StructSym)] =
      toArray(structSpecializations)

    def enqueueEnumSpecialization(sym: Symbol.EnumSym, targs: List[SimpleType])(implicit flix: Flix): Symbol.EnumSym =
      enumSpecializations.computeIfAbsent((sym, targs), entry => Symbol.freshEnumSym(entry._1))

    private def toArray[A <: AnyRef, B <: AnyRef](m: ConcurrentHashMap[(A, B), A]): Array[(A, B, A)] = {
      val res = mutable.ArrayBuffer.empty[(A, B, A)]
      val consumer = new BiConsumer[(A, B), A] {
        override def accept(t: (A, B), u: A): Unit =
          res.append((t._1, t._2, u))
      }
      m.forEach(consumer)
      res.toArray
    }

  }

}
