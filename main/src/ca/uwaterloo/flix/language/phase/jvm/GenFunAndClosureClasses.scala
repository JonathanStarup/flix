/*
 * Copyright 2021 Jonathan Lindegaard Starup
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

package ca.uwaterloo.flix.language.phase.jvm

import ca.uwaterloo.flix.api.Flix
import ca.uwaterloo.flix.language.ast.ReducedAst.{Def, Expr, Root}
import ca.uwaterloo.flix.language.ast.{Purity, ReducedAst, Symbol}
import ca.uwaterloo.flix.language.phase.jvm.BytecodeInstructions.*
import ca.uwaterloo.flix.language.phase.jvm.ClassMaker.Final.{IsFinal, NotFinal}
import ca.uwaterloo.flix.language.phase.jvm.ClassMaker.Visibility.IsPublic
import ca.uwaterloo.flix.language.phase.jvm.ClassMaker.Volatility.NotVolatile
import ca.uwaterloo.flix.util.ParOps
import org.objectweb.asm.{Label, MethodVisitor}

object GenFunAndClosureClasses {

  def gen(defs: Map[Symbol.DefnSym, Def])(implicit root: Root, flix: Flix): Map[JvmName, JvmClass] = {
    ParOps.parAgg(defs.values, Map.empty[JvmName, JvmClass])({
      case (macc, reducedDefn) =>
        flix.subtask(reducedDefn.sym.toString, sample = true)
        val defnClass = JvmOps.getDefnType(reducedDefn)
        val code = defnClass match {
          case defn: ClassMaker.Def => genDefn(defn, reducedDefn.expr)
          case defn: ClassMaker.EffectDef => genEffectDefn(defn, reducedDefn.expr)
          case closure: ClassMaker.Closure => genClosure(closure, reducedDefn.expr)
        }
        macc + (defnClass.jvmName -> JvmClass(defnClass.jvmName, code))
    }, _ ++ _)
  }

  private def genDefn(defn: ClassMaker.Def, exp: Expr)(implicit root: Root, flix: Flix): Array[Byte] = {
    val cm = ClassMaker.mkClass(defn.jvmName, IsFinal, defn.inheritedArrow.jvmName)

    cm.mkStaticMethod(defn.DirectApply, IsPublic, IsFinal, staticIns(exp)(_, root, flix))

    cm.mkConstructor(defn.Constructor, IsPublic, constructorIns(defn.inheritedArrow.Constructor)(_))
    cm.mkMethod(BackendObjType.Thunk.InvokeMethod.implementation(defn.jvmName), IsPublic, IsFinal, invokeViaStaticIns(defn)(_))

    cm.closeClassMaker()
  }

  private def genEffectDefn(defn: ClassMaker.EffectDef, exp: Expr)(implicit root: Root, flix: Flix): Array[Byte] = {
    val cm = ClassMaker.mkClass(defn.jvmName, IsFinal, superClass = defn.inheritedArrow.jvmName, interfaces = List(BackendObjType.Frame.jvmName))

    cm.mkConstructor(defn.Constructor, IsPublic, constructorIns(defn.inheritedArrow.Constructor)(_))

    for (i <- defn.locals.indices) cm.mkField(defn.LocalField(i), IsPublic, NotFinal, NotVolatile)
    cm.mkField(defn.PcField, IsPublic, NotFinal, NotVolatile)

    cm.mkMethod(BackendObjType.Thunk.InvokeMethod.implementation(defn.jvmName), IsPublic, IsFinal, invokeIns(defn.jvmName)(_))
    cm.mkMethod(BackendObjType.Frame.ApplyMethod.implementation(defn.jvmName), IsPublic, IsFinal, frameEffectIns(defn, exp)(_, root, flix))

    val pc = List(defn.PcField)
    val fparams = defn.args.indices.map(defn.inheritedArrow.ArgField)
    val lparams = defn.locals.indices.map(defn.LocalField)
    val fields = pc ++ fparams ++ lparams
    cm.mkMethod(defn.CopyMethod, IsPublic, IsFinal, copyIns(defn, fields)(_))

    cm.closeClassMaker()
  }

  private def genClosure(closure: ClassMaker.Closure, exp: Expr)(implicit root: Root, flix: Flix): Array[Byte] = {
    val cm = ClassMaker.mkClass(closure.jvmName, IsFinal, superClass = closure.superClass.jvmName, interfaces = List(BackendObjType.Frame.jvmName))

    cm.mkConstructor(closure.Constructor, IsPublic, constructorIns(closure.superClass.Constructor)(_))

    for (i <- closure.closureArgs.indices) cm.mkField(closure.CloArgField(i), IsPublic, NotFinal, NotVolatile)
    for (i <- closure.locals.indices) cm.mkField(closure.LocalField(i), IsPublic, NotFinal, NotVolatile)
    cm.mkField(closure.PcField, IsPublic, NotFinal, NotVolatile)

    cm.mkMethod(BackendObjType.Thunk.InvokeMethod.implementation(closure.jvmName), IsPublic, IsFinal, invokeIns(closure.jvmName)(_))

    cm.mkMethod(BackendObjType.Frame.ApplyMethod.implementation(closure.jvmName), IsPublic, IsFinal, frameClosureIns(closure, exp)(_, root, flix))

    val pc = List(closure.PcField)
    val fparams = closure.args.indices.map(closure.inheritedArrow.ArgField)
    val lparams = closure.locals.indices.map(closure.LocalField)
    val cparams = closure.closureArgs.indices.map(closure.CloArgField)
    val fields = pc ++ fparams ++ lparams ++ cparams
    cm.mkMethod(closure.CopyMethod, IsPublic, IsFinal, copyIns(closure, fields)(_))
    cm.mkMethod(closure.superClass.GetUniqueThreadClosureMethod.implementation(closure.jvmName), IsPublic, NotFinal, copyIns(closure, fields)(_))

    cm.closeClassMaker()
  }

  /** `superConstructor` must be a constructor without arguments. */
  private def constructorIns(superConstructor: ClassMaker.ConstructorMethod)(implicit mv: MethodVisitor): Unit = {
    assert(superConstructor.args.isEmpty)
    ALOAD(0)
    INVOKESPECIAL(superConstructor)
    RETURN()
  }

  private def staticIns(exp: ReducedAst.Expr)(implicit mv: MethodVisitor, root: Root, flix: Flix): Unit = {
    val enterLabel = new Label()
    mv.visitLabel(enterLabel)

    compileBody(exp, localOffset = 0, enterLabel)
  }

  private def invokeViaStaticIns(defnType: ClassMaker.Def)(implicit mv: MethodVisitor): Unit = {
    import BytecodeInstructions.*
    for ((arg, i) <- defnType.args.zipWithIndex) {
      thisLoad()
      GETFIELD(defnType.inheritedArrow.ArgField(i))
      BytecodeInstructions.castIfNotPrim(arg.tpe)
    }
    INVOKESTATIC(defnType.DirectApply)
    xReturn(BackendObjType.Result.toTpe)
  }

  private def invokeIns(className: JvmName)(implicit mv: MethodVisitor): Unit = {
    import BytecodeInstructions.*
    thisLoad()
    ACONST_NULL()
    INVOKEVIRTUAL(BackendObjType.Frame.ApplyMethod.implementation(className))
    xReturn(BackendObjType.Result.toTpe)
  }

  private def frameEffectIns(defn: ClassMaker.EffectDef, exp: Expr)(implicit mv: MethodVisitor, root: Root, flix: Flix): Unit = {
    import BytecodeInstructions.*

    val localOffset = 2 // [this: Obj, value: Obj, ...]

    for ((v, i) <- defn.locals.zipWithIndex) {
      thisLoad()
      GETFIELD(defn.LocalField(i))
      xStore(v.tpe, v.sym.getStackOffset(localOffset))
    }

    val enterLabel = new Label()
    mv.visitLabel(enterLabel)

    for ((v, i) <- defn.args.zipWithIndex) {
      thisLoad()
      GETFIELD(defn.inheritedArrow.ArgField(i))
      xStore(v.tpe, v.sym.getStackOffset(localOffset))
    }

    def newFrame(mv: MethodVisitor): Unit = {
      thisLoad()(mv)
      INVOKEVIRTUAL(defn.CopyMethod)(mv)
    }

    def setPc(mv: MethodVisitor): Unit = {
      SWAP()(mv)
      DUP_X1()(mv)
      SWAP()(mv) // clo, pc ---> clo, clo, pc
      PUTFIELD(defn.PcField)(mv)
      for ((v, i) <- defn.locals.zipWithIndex) {
        DUP()(mv)
        xLoad(v.tpe, v.sym.getStackOffset(localOffset))(mv)
        PUTFIELD(defn.LocalField(i))(mv)
      }
      POP()(mv)
    }

    val pcLabels: Vector[Label] = Vector.range(0, defn.pcPoints).map(_ => new Label())
    assert(defn.pcPoints > 0)
    // the default label is the starting point of the function if pc = 0
    val defaultLabel = new Label()
    ALOAD(0)
    GETFIELD(defn.PcField)
    mv.visitTableSwitchInsn(1, pcLabels.length, defaultLabel, pcLabels *)
    mv.visitLabel(defaultLabel)

    val ctx = GenExpression.EffectContext(enterLabel, Map.empty, newFrame, setPc, localOffset, pcLabels.prepended(null), Array(0))
    GenExpression.compileExpr(exp)(mv, ctx, root, flix)
    assert(ctx.pcCounter(0) == pcLabels.size, message = s"${(defn.jvmName.toBinaryName, ctx.pcCounter(0), pcLabels.size)}")
    xReturn(BackendObjType.Result.toTpe)
  }

  private def frameClosureIns(defn: ClassMaker.Closure, exp: Expr)(implicit mv: MethodVisitor, root: Root, flix: Flix): Unit = {
    import BytecodeInstructions.*
    val localOffset = 2 // [this: Obj, value: Obj, ...]

    for ((v, i) <- defn.locals.zipWithIndex) {
      thisLoad()
      GETFIELD(defn.LocalField(i))
      xStore(v.tpe, v.sym.getStackOffset(localOffset))
    }

    val enterLabel = new Label()
    mv.visitLabel(enterLabel)

    for ((v, i) <- defn.closureArgs.zipWithIndex) {
      thisLoad()
      GETFIELD(defn.CloArgField(i))
      xStore(v.tpe, v.sym.getStackOffset(localOffset))
    }
    for ((v, i) <- defn.args.zipWithIndex) {
      thisLoad()
      GETFIELD(defn.inheritedArrow.ArgField(i))
      xStore(v.tpe, v.sym.getStackOffset(localOffset))
    }

    if (Purity.isControlPure(exp.purity)) {
      val ctx = GenExpression.DirectInstanceContext(enterLabel, Map.empty, localOffset)
      GenExpression.compileExpr(exp)(mv, ctx, root, flix)
      xReturn(BackendObjType.Result.toTpe)
    } else {
      def newFrame(mv: MethodVisitor): Unit = {
        thisLoad()(mv)
        INVOKEVIRTUAL(defn.CopyMethod)(mv)
      }

      def setPc(mv: MethodVisitor): Unit = {
        SWAP()(mv)
        DUP_X1()(mv)
        SWAP()(mv) // clo, pc ---> clo, clo, pc
        PUTFIELD(defn.PcField)(mv)
        for ((v, i) <- defn.locals.zipWithIndex) {
          DUP()(mv)
          xLoad(v.tpe, v.sym.getStackOffset(localOffset))(mv)
          PUTFIELD(defn.LocalField(i))(mv)
        }
        POP()(mv)
      }

      val pcLabels: Vector[Label] = Vector.range(0, defn.pcPoints).map(_ => new Label())
      if (defn.pcPoints > 0) {
        // the default label is the starting point of the function if pc = 0
        val defaultLabel = new Label()
        ALOAD(0)
        GETFIELD(defn.PcField)
        mv.visitTableSwitchInsn(1, pcLabels.length, defaultLabel, pcLabels *)
        mv.visitLabel(defaultLabel)
      }

      val ctx = GenExpression.EffectContext(enterLabel, Map.empty, newFrame, setPc, localOffset, pcLabels.prepended(null), Array(0))
      GenExpression.compileExpr(exp)(mv, ctx, root, flix)
      assert(ctx.pcCounter(0) == pcLabels.size, message = s"${(defn.jvmName.toBinaryName, ctx.pcCounter(0), pcLabels.size)}")
      xReturn(BackendObjType.Result.toTpe)
    }
  }


  private def compileBody(exp: ReducedAst.Expr, localOffset: Int, enterLabel: Label)(implicit mv: MethodVisitor, root: Root, flix: Flix): Unit = {
    import BytecodeInstructions.*
    val ctx = GenExpression.DirectStaticContext(enterLabel, Map.empty, localOffset)
    GenExpression.compileExpr(exp)(mv, ctx, root, flix)
    xReturn(BackendObjType.Result.toTpe)
  }

  private def copyIns(defn: ClassMaker.DefClass, fields: List[ClassMaker.InstanceField])(implicit mv: MethodVisitor): Unit = {
    import BytecodeInstructions.*
    NEW(defn.jvmName)
    DUP()
    INVOKESPECIAL(defn.Constructor)
    for (field <- fields) {
      DUP()
      thisLoad()
      GETFIELD(field)
      PUTFIELD(field)
    }
    ARETURN()
  }

}
