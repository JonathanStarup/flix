package ca.uwaterloo.flix.language.phase

import ca.uwaterloo.flix.language.ast.NamedAst
import ca.uwaterloo.flix.language.ast.NamedAst.{Declaration, UseOrImport}
import ca.uwaterloo.flix.language.ast.Symbol
import ca.uwaterloo.flix.util.InternalCompilerException

import scala.collection.mutable

object ScopeGraph {

  object Root {
    val empty: Root[Nothing] = Root(Nil, Nil)

    def combine[Include](r1: Root[Include], r2: Root[Include]): Root[Include] = {
      Root(r1.blocks ++ r2.blocks, Module.combine(r1.modules ++ r2.modules))
    }
  }

  case class Root[+Include](blocks: List[File[Include]], modules: List[Module[Include]])

  case class Module[+Include](sym: Symbol.ModuleSym, blocks: List[File[Include]], modules: List[Module[Include]])

  object Module {
    def combine[Include](ms: List[Module[Include]]): List[Module[Include]] = {
      ms.groupBy(_.sym).map{
        case (_, mods) =>
          mods.reduceOption(combine[Include]).get
      }.toList
    }

    def combine[Include](m1: Module[Include], m2: Module[Include]): Module[Include] = {
      assert(m1.sym == m2.sym)
      Module(m1.sym, m1.blocks ++ m2.blocks, combine(m1.modules ++ m2.modules))
    }
  }

  sealed trait UseOrImport

  object UseOrImport {
    case class Use() extends UseOrImport
    case class Import() extends UseOrImport
  }

  case class File[+Include](includes: List[Include], decls: List[Decl])

  sealed trait Decl {
    def pub: Boolean
  }

  object Decl {
    case class Def(sym: Symbol.DefnSym, pub: Boolean) extends Decl
    case class Struct(sym: Symbol.StructSym, fields: List[Symbol.StructFieldSym], pub: Boolean) extends Decl
    case class Enum(sym: Symbol.EnumSym, cases: List[Symbol.CaseSym], pub: Boolean) extends Decl
    case class TypeAlias(sym: Symbol.TypeAliasSym, pub: Boolean) extends Decl
    // TODO more
  }

  def run(root: NamedAst.Root): Root[NamedAst.UseOrImport] = {
    val preGraph = root.units.values.map(visitUnit).reduceOption(Root.combine[NamedAst.UseOrImport]).getOrElse(Root.empty)
    val graph = resolveIncludes(graph)
    ???
  }

  private def visitUnit(unit: NamedAst.CompilationUnit): Root[NamedAst.UseOrImport] = {
    val NamedAst.CompilationUnit(usesAndImports, decls, _) = unit
    val (block, modules) = visitModule(usesAndImports, decls)
    Root(List(block), modules)
  }

  private def visitModule(usesAndImports: List[NamedAst.UseOrImport], decls0: List[NamedAst.Declaration]): (File[NamedAst.UseOrImport], List[Module[NamedAst.UseOrImport]]) = {
    val decls = new mutable.ArrayBuffer[Decl](decls0.size)
    val modules = new mutable.ArrayBuffer[Module[NamedAst.UseOrImport]](decls0.size)
    for (decl <- decls0) decl match {
      case Declaration.Namespace(sym, nestedUsesAndImports, nestedDecls, _) =>
        val (nestedBlock, nestedModules) = visitModule(nestedUsesAndImports, nestedDecls)
        modules.append(Module(sym, List(nestedBlock), nestedModules))
      case Declaration.Trait(doc, ann, mod, sym, tparam, superTraits, assocs, sigs, laws, loc) => ???
      case Declaration.Instance(doc, ann, mod, trt, tparams, tpe, tconstrs, assocs, defs, ns, loc) => ???
      case Declaration.Sig(sym, spec, exp, loc) => ???
      case Declaration.Def(sym, spec, _, _) =>
        decls.append(Decl.Def(sym, spec.mod.isPublic))
      case Declaration.Enum(_, _, mod, sym, _, _, cases, _) =>
        decls.append(Decl.Enum(sym, cases.map(_.sym), mod.isPublic))
      case Declaration.Struct(_, _, mod, sym, _, fields, _, _) =>
        decls.append(Decl.Struct(sym, fields.map(_.sym), mod.isPublic))
      case Declaration.RestrictableEnum(doc, ann, mod, sym, index, tparams, derives, cases, loc) => ???
      case Declaration.TypeAlias(_, _, mod, sym, _, _, _) =>
        decls.append(Decl.TypeAlias(sym, mod.isPublic))
      case Declaration.Effect(doc, ann, mod, sym, ops, loc) => ???
      case Declaration.StructField(_, _, _, loc) => throw InternalCompilerException(s"Unexpected declaration 'struct field' declaration", loc)
      case Declaration.AssocTypeSig(_, _, _, _, _, _, loc) => throw InternalCompilerException(s"Unexpected declaration 'associated type sig' declaration", loc)
      case Declaration.AssocTypeDef(_, _, _, _, _, loc) => throw InternalCompilerException(s"Unexpected declaration 'associated type def' declaration", loc)
      case Declaration.Op(_, _, loc) => throw InternalCompilerException(s"Unexpected declaration 'op' declaration", loc)
      case Declaration.Case(_, _, loc) => throw InternalCompilerException(s"Unexpected declaration 'case' declaration", loc)
      case Declaration.RestrictableCase(_, _, loc) => throw InternalCompilerException(s"Unexpected declaration 'restrictable case' declaration", loc)
    }
    (File(usesAndImports, decls.toList), modules.toList)
  }

  private def resolveIncludes(root: Root[NamedAst.UseOrImport]): Root[UseOrImport] = {
    val Root(blocks, modules) = root
    blocks.map(file => file.copy(includes = file.includes.map(resolve(_, root)))
  }

  private def resolve(uoi: NamedAst.UseOrImport, root: Root[NamedAst.UseOrImport]): UseOrImport = uoi match {
    case NamedAst.UseOrImport.Use(qname, alias, _) =>
      UseOrImport(alias, lookup(qname, root))
    case NamedAst.UseOrImport.Import(name, alias, loc) => ???
  }

}
