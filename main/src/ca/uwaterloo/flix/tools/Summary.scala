/*
 * Copyright 2023 Magnus Madsen
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package ca.uwaterloo.flix.tools

import ca.uwaterloo.flix.api.Flix
import ca.uwaterloo.flix.language.ast.TypedAst.{Expr, Root}
import ca.uwaterloo.flix.language.ast.{Ast, Kind, SourceLocation, SourcePosition, Type, TypedAst}
import ca.uwaterloo.flix.language.phase.typer.TypeConstraint
import ca.uwaterloo.flix.util.InternalCompilerException
import ca.uwaterloo.flix.language.ast.Symbol

import java.util.concurrent.ConcurrentHashMap
import scala.collection.immutable.SortedSet
import scala.collection.mutable.ListBuffer

object Summary {

  private val constraintSets: ConcurrentHashMap[Symbol, List[TypeConstraint]] = new ConcurrentHashMap()

  def addConstraints(defn: Symbol, cstrs: List[TypeConstraint])(implicit flix: Flix): Unit = {
    if (flix.options.xsummary) {
      if (constraintSets.containsKey(defn)) ???
      else {
        constraintSets.put(defn, cstrs)
      }
    }
  }

  /**
    * Returns a table of the file data of the root
    *
    * Example with markdown rendering (just a single data row):
    * {{{
    * |               Module |  lines |  defs |  Pure |  IO | Eff. Poly. |
    * | -------------------- | ------ | ----- | ----- | --- | ---------- |
    * |         Adaptor.flix |    242 |    21 |     8 |   5 |          8 |
    * |                  ... |    ... |   ... |   ... | ... |        ... |
    * |               Totals | 37,877 | 3,519 | 1,998 | 149 |      1,372 |
    * }}}
    *
    * @param root the root to create data for
    * @param nsDepth after this folder depth, files will be summarized under the
    *                folder
    * @param minLines all files with less lines than this will not be in the
    *                 table but it will still be reflected in the total row
    */
  def fileSummaryTable(root: Root, nsDepth: Option[Int], minLines: Option[Int]): Table = {
    val allSums = groupedFileSummaries(fileSummaries(root), nsDepth)
    val totals = fileTotals(allSums)
    val printedSums = minLines match {
      case Some(min) => allSums.filter(_.data.lines >= min)
      case None => allSums
    }
    val dots = printedSums.lengthIs < allSums.length
    val table = new Table()
    table.addRow(FileSummary.header)
    printedSums.sortBy(_.src.name).map(_.toRow).foreach(table.addRow)
    if (dots) table.addRepeatedRow("...")
    table.addRow("Totals" :: totals.toRow)
    table
  }

  def effectVariableTable(root: Root): Table = {
    val sums = defSummaries(root)
    val defCount = sums.length
    val varSums = sums.map(s => {
      val i = instanceEffectVariables(s)
      val d = defEffectVariables(s)
      if (!((i <= 1 && d == 0) || (i == 0 && d <= 1))) ???
      (lambdaEffectVariables(s), i, d)
    })
    val totalEffVars = sums.map(_.effVars).sum
    val (lambdaAffected, instanceAffected, defAffected) = varSums.foldLeft((0, 0, 0)){
      case ((lamAcc, insAcc, defAcc), (lamCur, insCur, defCur)) =>
        (lamAcc + (lamCur min 1), insAcc + (insCur min 1), defAcc + (defCur min 1))
    }
    val (lambdaTotal, instanceTotal, defTotal) = varSums.foldLeft((0, 0, 0)) {
      case ((lamAcc, insAcc, defAcc), (lamCur, insCur, defCur)) =>
        (lamAcc + lamCur, insAcc + insCur, defAcc + defCur)
    }
    val (lambdaMax, instanceMax, defMax) = varSums.foldLeft((0, 0, 0)) {
      case ((lamAcc, insAcc, defAcc), (lamCur, insCur, defCur)) =>
        (lamAcc max lamCur, insAcc max insCur, defAcc max defCur)
    }
    val table = new Table()
    println(totalEffVars)
    table.addRow(List("Abstraction-site", "variable increase", "%", "defs affected", "%", "inc. max"))
    table.addRow(List("Lambda", format(lambdaTotal), formatP(100*(lambdaTotal + totalEffVars)/(1.0*totalEffVars) - 100), format(lambdaAffected), formatP(100*lambdaAffected/(1.0 * defCount)), format(lambdaMax)))
    table.addRow(List("Instance", format(instanceTotal), formatP(100*(instanceTotal + totalEffVars)/(1.0*totalEffVars) - 100), format(instanceAffected), formatP(100*instanceAffected/(1.0 * defCount)), format(instanceMax)))
    table.addRow(List("Def", format(defTotal), formatP(100*(defTotal + totalEffVars)/(1.0*totalEffVars) - 100), format(defAffected), formatP(100*defAffected/(1.0 * defCount)), format(defMax)))
    table
  }

  private def lambdaEffectVariables(sum: DefSummary): Int = {
    sum.lambdas
  }

  private def instanceEffectVariables(sum: DefSummary): Int = {
    if (!sum.fun.isInstanceOf[FunctionSym.InstanceFun]) 0
    else if (sum.eff == ResEffect.Pure) 0
    else 1
  }

  private def defEffectVariables(sum: DefSummary): Int = {
    if (sum.fun.isInstanceOf[FunctionSym.InstanceFun]) 0
    else if (sum.eff == ResEffect.Pure) 0
    else 1
  }

  /** Returns a function summary for a def or an instance, depending on the flag */
  private def defSummary(defn: TypedAst.Def, isInstance: Boolean): DefSummary = {
    val fun = if (isInstance) FunctionSym.InstanceFun(defn.sym) else FunctionSym.Def(defn.sym)
    val ls = lambdas(defn.exp)
    val es = effVars(defn.sym)
    val eff = resEffect(defn.spec.eff)
    DefSummary(fun, ls, es, eff)
  }

  /** Returns a function summary for a signature, if it has implementation */
  private def defSummary(sig: TypedAst.Sig): Option[DefSummary] = sig.exp match {
    case None => None
    case Some(exp) =>
      val fun = FunctionSym.TraitFunWithExp(sig.sym)
      val ls = lambdas(exp)
      val es = effVars(sig.sym)
      val eff = resEffect(sig.spec.eff)
      Some(DefSummary(fun, ls, es, eff))
  }

  /** Returns a function summary for every function */
  private def defSummaries(root: Root): List[DefSummary] = {
    val defs = root.defs.values.map(defSummary(_, isInstance = false))
    val instances = root.instances.values.flatten.flatMap(_.defs.map(defSummary(_, isInstance = true)))
    val traits = root.traits.values.flatMap(_.sigs.flatMap(defSummary))
    (defs ++ instances ++ traits).toList
  }

  /** Converts a function summary into file data.
    * Root is used to find file length.
    */
  private def fileData(sum: DefSummary)(implicit root: Root): FileData = {
    val src = sum.fun.loc.source
    val srcLoc = root.sources.getOrElse(src, SourceLocation(isReal = false, SourcePosition(unknownSource, 0, 0), SourcePosition(unknownSource, 0, 0)))
    val pureDefs = if (sum.eff == ResEffect.Pure) 1 else 0
    val justIODefs = if (sum.eff == ResEffect.JustIO) 1 else 0
    val polyDefs = if (sum.eff == ResEffect.Poly) 1 else 0
    FileData(Some(src), srcLoc.endLine, defs = 1, pureDefs, justIODefs, polyDefs)
  }

  /** Combines function summaries into file data. */
  private def fileData(sums: List[DefSummary])(implicit root: Root): FileData = {
    FileData.combine(sums.map(fileData))
  }

  /** Returns a file summary of each individual file. */
  private def fileSummaries(root: Root): List[FileSummary] = {
    val defSums = defSummaries(root)
    defSums.groupBy(_.src).map { case (src, sums) => FileSummary(src, fileData(sums)(root)) }.toList
  }

  /**
    * Returns the given summaries grouped by their folder structure up to the
    * given depth if any. If depth 1 is given, then top level folders are
    * summarized by a single summary.
    *
    * Sources are converted to faux sources to reflect the groupings.
    *
    * nsDepth=1 means that `Something/One.flix` and `Something/Two.flix` are
    * counted together under `Something/...`. nsDepth=2 would keep them separate
    * but collect files a level deeper.
    *
    * nsDepth < 1 means all files are kept separate.
    */
  private def groupedFileSummaries(sums: List[FileSummary], nsDepth: Option[Int]): List[FileSummary] = {
    def comb(x: FileSummary, y: FileSummary): FileSummary = {
      FileSummary(x.src, x.data.naiveSum(y.data))
    }

    def zero(name: String): FileSummary =
      FileSummary(Ast.Source(Ast.Input.Text(name, "", stable = true), Array.emptyCharArray, stable = true), FileData.zero)

    sums.groupBy(sum => prefixFileName(sum.src.name, nsDepth)).map {
      case (_, List(sum)) => sum
      case (name, sums) => sums.foldLeft(zero(name))(comb).copy(src = zero(name).src)
    }.toList
  }

  /**
    * - prefixFileName("a/b", None) = "a/b"
    * - prefixFileName("a/b", Some(1)) = "a/..."
    * - prefixFileName("a/b", Some(2)) = "a/b"
    * - prefixFileName("a/b/c", Some(2)) = "a/b/..."
    * - prefixFileName("a/b", Some(0) = "a/b"
    * - prefixFileName("a/b", Some(-1) = "a/b"
    */
  private def prefixFileName(name: String, nsDepth: Option[Int]): String = {
    nsDepth match {
      case None => name
      case Some(depth) =>
        // Note: the separator disagrees with File.separator
        val fileSep = '/'
        name.split(fileSep).toList match {
          case parts if depth > 0 && parts.length > depth =>
            (parts.take(depth) :+ "...").mkString(fileSep.toString)
          case _ => name
        }
    }
  }

  private def fileTotals(l: List[FileSummary]): FileData = {
    FileData.naiveSum(l.map(_.data))
  }

  /**
    * Assumes that IO and Pure are represented simply, i.e. no `{} + {}`,
    * `IO + {}`, or `x - x`.
    */
  private def resEffect(eff: Type): ResEffect = eff match {
    case Type.Pure => ResEffect.Pure
    case Type.IO => ResEffect.JustIO
    case _ if eff.kind == Kind.Eff => ResEffect.Poly
    case _ => throw InternalCompilerException(s"Not an effect: '$eff'", eff.loc)
  }

  private def effVars(sym: Symbol): Int = {
    if (constraintSets.containsKey(sym)) {
      effVars(constraintSets.get(sym))
    } else ???
  }

  private def effVars(l: List[TypeConstraint]): Int = {
    l.foldLeft(SortedSet.empty[Type.Var]){case (acc, c) => acc ++ effVars(c)}.size
  }

  private def effVars(t: TypeConstraint): SortedSet[Type.Var] = {
    vars(t).filter(_.kind == Kind.Eff)
  }

  private def vars(l: List[TypeConstraint]): SortedSet[Type.Var] = {
    l.foldLeft(SortedSet.empty[Type.Var]){case (acc, c) => acc ++ vars(c)}
  }

  private def vars(t: TypeConstraint): SortedSet[Type.Var] = t match {
    case TypeConstraint.Equality(tpe1, tpe2, _) =>
      tpe1.typeVars ++ tpe2.typeVars
    case TypeConstraint.EqJvmConstructor(cvar, _, tpes, _) =>
      SortedSet(cvar) ++ tpes.map(_.typeVars).foldLeft(SortedSet.empty[Type.Var])((a, b) => a ++ b)
    case TypeConstraint.EqJvmMethod(mvar, tpe0, _, tpes, _) =>
      SortedSet(mvar) ++ tpe0.typeVars ++ tpes.map(_.typeVars).foldLeft(SortedSet.empty[Type.Var])((a, b) => a ++ b)
    case TypeConstraint.EqStaticJvmMethod(mvar, _, _, tpes, _) =>
      SortedSet(mvar) ++ tpes.map(_.typeVars).foldLeft(SortedSet.empty[Type.Var])((a, b) => a ++ b)
    case TypeConstraint.Trait(_, tpe, _) =>
      tpe.typeVars
    case TypeConstraint.Purification(_, eff1, eff2, _, nested) =>
      eff1.typeVars ++ eff2.typeVars ++ vars(nested)
  }

  private def lambdas(l: List[Expr]): Int = {
    l.map(lambdas).sum
  }

  /**
    * Returns the number of syntactic lambdas in the function body.
    *
    * OBS: newObject is not counted as a lambda.
    */
  private def lambdas(e: Expr): Int = {
    e match {
      case Expr.Lambda(_, exp, _, _) => 1 + lambdas(exp)

      case Expr.Cst(_, _, _) => 0
      case Expr.Var(_, _, _) => 0
      case Expr.Def(_, _, _) => 0
      case Expr.Sig(_, _, _) => 0
      case Expr.Hole(_, _, _) => 0
      case Expr.HoleWithExp(exp, _, _, _) => lambdas(exp)
      case Expr.OpenAs(_, exp, _, _) => lambdas(exp)
      case Expr.Use(_, _, exp, _) => lambdas(exp)
      case Expr.Apply(exp, exps, _, _, _) => lambdas(exp :: exps)
      case Expr.Unary(_, exp, _, _, _) => lambdas(exp)
      case Expr.Binary(_, exp1, exp2, _, _, _) => lambdas(exp1) + lambdas(exp2)
      case Expr.Let(_, _, exp1, exp2, _, _, _) => lambdas(exp1) + lambdas(exp2)
      case Expr.LetRec(_, _, _, exp1, exp2, _, _, _) => lambdas(exp1) + lambdas(exp2)
      case Expr.Region(_, _) => 0
      case Expr.Scope(_, _, exp, _, _, _) => lambdas(exp)
      case Expr.IfThenElse(exp1, exp2, exp3, _, _, _) => lambdas(exp1) + lambdas(exp2) + lambdas(exp3)
      case Expr.Stm(exp1, exp2, _, _, _) => lambdas(exp1) + lambdas(exp2)
      case Expr.Discard(exp, _, _) => lambdas(exp)
      case Expr.Match(exp, rules, _, _, _) => lambdas(exp :: rules.flatMap(r => r.exp :: r.guard.toList))
      case Expr.TypeMatch(exp, rules, _, _, _) => lambdas(exp :: rules.map(_.exp))
      case Expr.RestrictableChoose(_, exp, rules, _, _, _) => lambdas(exp :: rules.map(_.exp))
      case Expr.Tag(_, exp, _, _, _) => lambdas(exp)
      case Expr.RestrictableTag(_, exp, _, _, _) => lambdas(exp)
      case Expr.Tuple(elms, _, _, _) => lambdas(elms)
      case Expr.RecordEmpty(_, _) => 0
      case Expr.RecordSelect(exp, _, _, _, _) => lambdas(exp)
      case Expr.RecordExtend(_, exp1, exp2, _, _, _) => lambdas(exp1) + lambdas(exp2)
      case Expr.RecordRestrict(_, exp, _, _, _) => lambdas(exp)
      case Expr.ArrayLit(exps, exp, _, _, _) => lambdas(exp :: exps)
      case Expr.ArrayNew(exp1, exp2, exp3, _, _, _) => lambdas(exp1) + lambdas(exp2) + lambdas(exp3)
      case Expr.ArrayLoad(exp1, exp2, _, _, _) => lambdas(exp1) + lambdas(exp2)
      case Expr.ArrayLength(exp, _, _) => lambdas(exp)
      case Expr.ArrayStore(exp1, exp2, exp3, _, _) => lambdas(exp1) + lambdas(exp2) + lambdas(exp3)
      case Expr.VectorLit(exps, _, _, _) => lambdas(exps)
      case Expr.VectorLoad(exp1, exp2, _, _, _) => lambdas(exp1) + lambdas(exp2)
      case Expr.VectorLength(exp, _) => lambdas(exp)
      case Expr.Ref(exp1, exp2, _, _, _) => lambdas(exp1) + lambdas(exp2)
      case Expr.Deref(exp, _, _, _) => lambdas(exp)
      case Expr.Assign(exp1, exp2, _, _, _) => lambdas(exp1) + lambdas(exp2)
      case Expr.Ascribe(exp, _, _, _) => lambdas(exp)
      case Expr.InstanceOf(exp, _, _) => lambdas(exp)
      case Expr.CheckedCast(_, exp, _, _, _) => lambdas(exp)
      case Expr.UncheckedCast(exp, _, _, _, _, _) => lambdas(exp)
      case Expr.UncheckedMaskingCast(exp, _, _, _) => lambdas(exp)
      case Expr.Without(exp, _, _, _, _) => lambdas(exp)
      case Expr.TryCatch(exp, rules, _, _, _) => lambdas(exp :: rules.map(_.exp))
      case Expr.TryWith(exp, _, rules, _, _, _) => lambdas(exp :: rules.map(_.exp))
      case Expr.Do(_, exps, _, _, _) => lambdas(exps)
      case Expr.InvokeConstructor(_, exps, _, _, _) => lambdas(exps)
      case Expr.InvokeMethod(_, exp, exps, _, _, _) => lambdas(exp :: exps)
      case Expr.InvokeStaticMethod(_, exps, _, _, _) => lambdas(exps)
      case Expr.GetField(_, exp, _, _, _) => lambdas(exp)
      case Expr.PutField(_, exp1, exp2, _, _, _) => lambdas(exp1) + lambdas(exp2)
      case Expr.GetStaticField(_, _, _, _) => 0
      case Expr.PutStaticField(_, exp, _, _, _) => lambdas(exp)
      case Expr.NewObject(_, _, _, _, methods, _) => lambdas(methods.map(_.exp))
      case Expr.NewChannel(exp1, exp2, _, _, _) => lambdas(exp1) + lambdas(exp2)
      case Expr.GetChannel(exp, _, _, _) => lambdas(exp)
      case Expr.PutChannel(exp1, exp2, _, _, _) => lambdas(exp1) + lambdas(exp2)
      case Expr.SelectChannel(rules, default, _, _, _) => lambdas(default.toList ++ rules.flatMap(r => List(r.exp, r.chan)))
      case Expr.Spawn(exp1, exp2, _, _, _) => lambdas(exp1) + lambdas(exp2)
      case Expr.ParYield(frags, exp, _, _, _) => lambdas(exp :: frags.map(_.exp))
      case Expr.Lazy(exp, _, _) => lambdas(exp)
      case Expr.Force(exp, _, _, _) => lambdas(exp)
      case Expr.FixpointConstraintSet(cs, _, _) => cs.flatMap(_.head match {
        case TypedAst.Predicate.Head.Atom(_, _, terms, _, _) => terms
      }).map(lambdas).sum
      case Expr.FixpointLambda(_, exp, _, _, _) => lambdas(exp)
      case Expr.FixpointMerge(exp1, exp2, _, _, _) => lambdas(exp1) + lambdas(exp2)
      case Expr.FixpointSolve(exp, _, _, _) => lambdas(exp)
      case Expr.FixpointFilter(_, exp, _, _, _) => lambdas(exp)
      case Expr.FixpointInject(exp, _, _, _, _) => lambdas(exp)
      case Expr.FixpointProject(_, exp, _, _, _) => lambdas(exp)
      case Expr.Error(_, _, _) => 0
    }
  }

  private val unknownSource = {
    Ast.Source(Ast.Input.Text("generated", "", stable = true), Array.emptyCharArray, stable = true)
  }

  /** debugSrc is just for consistency checking exceptions */
  private sealed case class FileData(debugSrc: Option[Ast.Source], lines: Int, defs: Int, pureDefs: Int, justIODefs: Int, polyDefs: Int) {
    if (defs != pureDefs + justIODefs + polyDefs) {
      val src = debugSrc.getOrElse(unknownSource)
      throw InternalCompilerException(
        s"${(defs, pureDefs, justIODefs, polyDefs)} does not sum for $src",
        SourceLocation(isReal = true, SourcePosition(src, 0, 0), SourcePosition(src, 0, 0))
      )
    }

    /**
      * Combines two partial FileData from the same file. Line count is asserted
      * to be equal for both data and is left unchanged. The remaining fields
      * are summed.
      */
    def combine(other: FileData): FileData = {
      if (lines != other.lines) {
        val src = debugSrc.getOrElse(unknownSource)
        throw InternalCompilerException(s"lines '$lines' and '${other.lines}' in $debugSrc",
          SourceLocation(isReal = true, SourcePosition(src, 0, 0), SourcePosition(src, 0, 0))
        )
      }
      FileData(debugSrc.orElse(other.debugSrc), lines, defs + other.defs, pureDefs + other.pureDefs, justIODefs + other.justIODefs, polyDefs + other.polyDefs)
    }

    /**
      * Returns new data where each field is summed. This is used for data of
      * different files to compute a total of a folder fx.
      */
    def naiveSum(other: FileData): FileData = {
      FileData(debugSrc.orElse(other.debugSrc), lines + other.lines, defs + other.defs, pureDefs + other.pureDefs, justIODefs + other.justIODefs, polyDefs + other.polyDefs)
    }

    def toRow: List[String] = List(lines, defs, pureDefs, justIODefs, polyDefs).map(format)
  }

  private object FileData {
    val zero: FileData = FileData(None, 0, 0, 0, 0, 0)

    /**
      * Combines a list of partial FileData from the same file. Line count is
      * asserted to be equal for all data and is left unchanged. The remaining
      * fields are summed.
      */
    def combine(l: List[FileData]): FileData = if (l.nonEmpty) l.reduce(_.combine(_)) else zero

    /**
      * Returns new data where each field is summed. This is used for data of
      * different files to compute a total of a folder fx.
      */
    def naiveSum(l: List[FileData]): FileData = if (l.nonEmpty) l.reduce(_.naiveSum(_)) else zero

    def header: List[String] = List("lines", "defs", "Pure", "IO", "Eff. Poly.")
  }

  private sealed case class FileSummary(src: Ast.Source, data: FileData) {
    def toRow: List[String] = List(src.name) ++ data.toRow
  }

  private object FileSummary {
    def header: List[String] = List("Module") ++ FileData.header
  }

  private sealed case class DefSummary(fun: FunctionSym, lambdas: Int, effVars: Int, eff: ResEffect) {
    def src: Ast.Source = loc.source

    def loc: SourceLocation = fun.loc
  }

  /**
    * Represents the direct effect of a function
    * - `def f(x: Int32): Int32` is `Pure`
    * - `def f(x: Int32): Unit \ IO` is `JustIO`
    * - `def f(x: Array[Int32, r]): IO + r` is `Poly`
    */
  private sealed trait ResEffect

  private object ResEffect {
    case object Pure extends ResEffect

    case object JustIO extends ResEffect

    case object Poly extends ResEffect
  }

  /**
    * This type is used to differentiate between
    * - normal defs
    * - instance defs, and
    * - trait defs with implementation
    */
  private sealed trait FunctionSym {
    def loc: SourceLocation
  }

  private object FunctionSym {

    import ca.uwaterloo.flix.language.ast.Symbol

    case class Def(sym: Symbol.DefnSym) extends FunctionSym {
      val loc: SourceLocation = sym.loc
    }

    case class TraitFunWithExp(sym: Symbol.SigSym) extends FunctionSym {
      val loc: SourceLocation = sym.loc
    }

    case class InstanceFun(sym: Symbol.DefnSym) extends FunctionSym {
      val loc: SourceLocation = sym.loc
    }
  }

  /** Formats the given number `n`. */
  private def format(n: Int): String = f"$n%,d".replace(".", ",")


  /** Formats the given number `n`. */
  private def formatP(n: Double): String = f"$n%,.0f".replace(".", ",") + " %"

  /** Right-pads the given string `s` to length `l`. */
  private def padR(s: String, l: Int): String = s.padTo(l, ' ')

  /** Left-pads the given string `s` to length `l`. */
  private def padL(s: String, l: Int): String = {
    if (s.length >= l) {
      return s
    }
    val sb = new StringBuilder
    while (sb.length < l - s.length) {
      sb.append(' ')
    }
    sb.append(s)
    sb.toString
  }

  /** Keeps track of max lengths in columns */
  class Table() {

    /** The rows collected so far */
    private val rows: ListBuffer[List[String]] = ListBuffer.empty

    /**
      * Has the length of the longest list in rows. Each integer contains the
      * max length of any string in that column.
      */
    private val maxLens: ListBuffer[Int] = ListBuffer.empty

    /** Adds a row to the builder. The rows can have different lengths */
    def addRow(row: List[String]): Unit = insertRow(rows.length, row)

    private def insertRow(idx: Int, row: List[String]): Unit = {
      for ((s, i) <- row.iterator.zipWithIndex) {
        if (i >= maxLens.size) maxLens.append(0)
        maxLens(i) = maxLens(i) max s.length
      }
      rows.insert(idx, row)
    }

    /**
      * Adds a row with the given content in each column. The number of columns
      * is the max length of the previous columns.
      *
      * OBS: if this is the first row, it will have zero columns.
      */
    def addRepeatedRow(content: String): Unit = {
      addRow(maxLens.toList.map(_ => content))
    }

    /**
      * Returns the built rows where all strings are left padded to have
      * consistent column lengths, i.e, all strings in a column is padded to the
      * length of the longest string in the column.
      */
    def getRows: List[List[String]] = {
      rows.map(row => {
        row.iterator.zipWithIndex.map {
          case (s, i) => padL(s, maxLens(i))
        }.toList
      }).toList
    }

    /** Returns the table as a list of lines with latex formatting. */
    def getLatexLines: List[String] = {
      // avoid common illegal character % in latex syntax
      def sanitize(s: String): String = s.replace("%", "\\%")

      def latexLine(l: List[String]): String = l.mkString("", " & ", " \\\\")

      getRows.map(_.map(sanitize)).map(latexLine)
    }

    /** Returns the table as a list of lines with markdown formatting */
    def getMarkdownLines: List[String] = {
      // add | --- | --- | --- | header separation
      if (rows.length >= 2) {
        insertRow(1, maxLens.toList.map(len => "-" * (len max 3)))
      }

      def markdownLine(l: List[String]): String = l.mkString("| ", " | ", " |")

      getRows.map(markdownLine)
    }
  }

}
