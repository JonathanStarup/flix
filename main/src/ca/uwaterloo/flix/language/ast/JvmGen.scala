package ca.uwaterloo.flix.language.ast

import ca.uwaterloo.flix.api.Flix
import ca.uwaterloo.flix.language.ast.LowLevelAst.{Def, Exp, Root}
import ca.uwaterloo.flix.language.dbg.AstPrinter
import ca.uwaterloo.flix.language.phase.jvm.BackendObjType
import ca.uwaterloo.flix.language.phase.jvm.BytecodeInstructions.*
import org.objectweb.asm.MethodVisitor

object JvmGen {

  def run(root: Root)(implicit flix: Flix): Unit = flix.phase("") {
    val defClasses = root.defs.values.map(visitDef)
  }(AstPrinter.DebugNoOp())

  private def visitDef(defn: Def): Array[Byte] = {
    ???
  }

  private def visitExp(exp: Exp)(implicit mv: MethodVisitor): Unit = exp match {
    case Exp.Unit =>
      GETSTATIC(BackendObjType.Unit.SingletonField)

    case Exp.Null =>
      ACONST_NULL()
  }

}
