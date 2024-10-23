/*
 * Copyright 2023 Jonathan Lindegaard Starup
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

package ca.uwaterloo.flix.language.dbg.printer

import ca.uwaterloo.flix.language.ast.MonoAst.Expr.*
import ca.uwaterloo.flix.language.ast.{MonoAst, Symbol}
import ca.uwaterloo.flix.language.dbg.DocAst
import ca.uwaterloo.flix.util.collection.MapOps

object MonoAstPrinter {

  /**
    * Returns the [[DocAst.Program]] representation of `root`.
    */
  def print(root: MonoAst.Root): DocAst.Program = {
    val defs = root.defs.values.map {
      case MonoAst.Def(sym, MonoAst.Spec(_, ann, mod, formals, _, tpe, eff), exp, _) =>
        DocAst.Def(
          ann,
          mod,
          sym,
          formals.map(printFormalParam),
          TypePrinter.print(tpe),
          TypePrinter.printAsEffect(eff),
          print(exp)
        )
    }.toList
    DocAst.Program(Nil, defs)
  }

  /**
    * Returns the [[DocAst.Expr]] representation of `e`.
    */
  def print(e: MonoAst.Expr): DocAst.Expr = e match {
    case Cst(cst, _, _) => ConstantPrinter.print(cst)
    case Var(sym, _, _) => printVarSym(sym)
    case Lambda(fparam, exp, _, _) => DocAst.Expr.Lambda(List(printFormalParam(fparam)), print(exp))
    case ApplyAtomic(op, exps, tpe, _, _) => OpPrinter.print(op, exps.map(print), TypePrinter.print(tpe))
    case ApplyClo(exp, args, _, _, _) => DocAst.Expr.ApplyClo(print(exp), args.map(print), None)
    case ApplyDef(sym, exps, _, _, _, _) => DocAst.Expr.ApplyDef(sym, exps.map(print), None)
    case ApplyLocalDef(sym, exps, _, _, _) => DocAst.Expr.ApplyClo(printVarSym(sym), exps.map(print), None)
    case IfThenElse(exp1, exp2, exp3, _, _, _) => DocAst.Expr.IfThenElse(print(exp1), print(exp2), print(exp3))
    case Stm(exp1, exp2, _, _, _) => DocAst.Expr.Stm(print(exp1), print(exp2))
    case Discard(exp, _, _) => DocAst.Expr.Discard(print(exp))
    case Match(exp, rules, _, _, _) => DocAst.Expr.Match(print(exp), rules.map{
      case MonoAst.MatchRule(pat, guard, exp) => (printPattern(pat), guard.map(print), print(exp))
    })
    case VectorLit(exps, _, _, _) => DocAst.Expr.VectorLit(exps.map(print))
    case VectorLoad(exp1, exp2, _, _, _) => DocAst.Expr.VectorLoad(print(exp1), print(exp2))
    case VectorLength(exp, _) => DocAst.Expr.VectorLength(print(exp))
    case Ascribe(exp, tpe, _, _) => DocAst.Expr.Ascription(print(exp), TypePrinter.print(tpe))
    case Cast(exp, _, _, tpe, _, _) => DocAst.Expr.Cast(print(exp), TypePrinter.print(tpe))
    case Let(sym, exp1, exp2, _, _, _) => DocAst.Expr.Let(printVarSym(sym), Some(TypePrinter.print(exp1.tpe)), print(exp1), print(exp2))
    case LocalDef(sym, _, exp1, exp2, _, _, _) => DocAst.Expr.LetRec(printVarSym(sym), Some(TypePrinter.print(exp1.tpe)), print(exp1), print(exp2))
    case Scope(sym, _, exp, _, _, _) => DocAst.Expr.Scope(printVarSym(sym), print(exp))
    case TryCatch(exp, rules, _, _, _) => DocAst.Expr.TryCatch(print(exp), rules.map {
      case MonoAst.CatchRule(sym, clazz, exp) =>
        (sym, clazz, print(exp))
    })
    case TryWith(exp, effUse, rules, _, _, _) => DocAst.Expr.TryWith(print(exp), effUse.sym, rules.map {
      case MonoAst.HandlerRule(op, fparams, exp) =>
        (op.sym, fparams.map(printFormalParam), print(exp))
    })
    case Do(op, exps, _, _, _) => DocAst.Expr.Do(op.sym, exps.map(print))
    case NewObject(name, clazz, tpe, _, methods, _) => DocAst.Expr.NewObject(name, clazz, TypePrinter.print(tpe), methods.map {
      case MonoAst.JvmMethod(ident, fparams, exp, retTpe, _, _) =>
        DocAst.JvmMethod(ident, fparams.map(printFormalParam), print(exp), TypePrinter.print(retTpe))
    })
  }

  /**
    * Returns the [[DocAst.Expr.Ascription]] representation of `fp`.
    */
  private def printFormalParam(fp: MonoAst.FormalParam): DocAst.Expr.Ascription = {
    val MonoAst.FormalParam(sym, _, tpe, _, _) = fp
    DocAst.Expr.Ascription(printVarSym(sym), TypePrinter.print(tpe))
  }

  /**
    * Returns the [[DocAst.Expr]] representation of `sym`.
    */
  private def printVarSym(sym: Symbol.VarSym): DocAst.Expr =
    DocAst.Expr.Var(sym)

  /**
    * Returns the [[DocAst.Expr]] representation of `pattern`.
    */
  private def printPattern(pattern: MonoAst.Pattern): DocAst.Expr = pattern match {
    case MonoAst.Pattern.Wild(_, _) => DocAst.Expr.Wild
    case MonoAst.Pattern.Var(sym, _, _) => printVarSym(sym)
    case MonoAst.Pattern.Cst(cst, _, _) => ConstantPrinter.print(cst)
    case MonoAst.Pattern.Tag(sym, pat, _, _) => DocAst.Expr.Tag(sym.sym, List(printPattern(pat)))
    case MonoAst.Pattern.Tuple(elms, _, _) => DocAst.Expr.Tuple(elms.map(printPattern))
    case MonoAst.Pattern.Record(pats, pat, _, _) => printRecordPattern(pats, pat)
    case MonoAst.Pattern.RecordEmpty(_, _) => DocAst.Expr.RecordEmpty
  }

  /** Returns the [[DocAst.Expr]] representation of `pats`. */
  private def printRecordPattern(pats: List[MonoAst.Pattern.Record.RecordLabelPattern], pat: MonoAst.Pattern): DocAst.Expr = {
    pats.foldRight(printPattern(pat)) {
      case (MonoAst.Pattern.Record.RecordLabelPattern(label, _, pat, _), acc) =>
        DocAst.Expr.RecordExtend(label, printPattern(pat), acc)
    }
  }

}
