/*
 * Copyright 2024 Matthew Lutze
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
package ca.uwaterloo.flix.language.phase.typer

import ca.uwaterloo.flix.api.Flix
import ca.uwaterloo.flix.language.ast.shared.Scope
import ca.uwaterloo.flix.language.ast.{Ast, RigidityEnv, SourceLocation, Symbol, Type, TypeConstructor}
import ca.uwaterloo.flix.language.errors.TypeError
import ca.uwaterloo.flix.language.phase.unification.Unification
import ca.uwaterloo.flix.util.{InternalCompilerException, Result}
import ca.uwaterloo.flix.util.collection.{ListMap, ListOps}

import java.lang.reflect.Method
import java.lang.reflect.Constructor
import java.math.BigInteger
import scala.annotation.tailrec

object TypeReduction {

  /**
   * Simplifies the given type by reducing associated type applications.
   *
   * Θ ⊩ τ ⤳ τ'
   *
   * Returns the simplified type and a Boolean flag to indicate whether progress was made.
   *
   * Applications that cannot be resolved are left as they are.
   * These are applications to variables and applications to other unresolvable types.
   *
   * Applications that are illegal result in an Err.
   * These are applications to types for which the eqEnv has no corresponding instance.
   *
   * For example:
   * {{{
   *   Int           ~> Int
   *   Elm[List[a]]  ~> a
   *   Elm[Int]      ~> <ERROR>
   *   Elm[Elm[a]]   ~> Elm[Elm[a]]
   * }}}
   */
  def simplify(tpe: Type, renv0: RigidityEnv, loc: SourceLocation)(implicit scope: Scope, eenv: ListMap[Symbol.AssocTypeSym, Ast.AssocTypeDef], flix: Flix): Result[(Type, Boolean), TypeError] = tpe match {
    // A var is already simple.
    case t: Type.Var => Result.Ok((t, false))

    // A constant is already simple
    case t: Type.Cst => Result.Ok((t, false))

    // lapp_L and lapp_R
    case Type.Apply(tpe1, tpe2, loc) =>
      for {
        (t1, p1) <- simplify(tpe1, renv0, loc)
        (t2, p2) <- simplify(tpe2, renv0, loc)
        (t3, p3) <- simplifyJava(Type.Apply(t1, t2, loc), renv0, loc)
      } yield {
        (t3, p1 || p2 || p3)
      }

    // arg_R and syn_R
    case Type.AssocType(cst, arg, kind, _) =>
      simplify(arg, renv0, loc).flatMap {
        case (t, p) =>
          // we mark t's tvars as rigid so we get the substitution in the right direction
          val renv = t.typeVars.map(_.sym).foldLeft(RigidityEnv.empty)(_.markRigid(_))
          val insts = eenv(cst.sym)

          // find the first (and only) instance that matches
          val simplifiedOpt = ListOps.findMap(insts) {
            inst =>
              Unification.unifyTypes(t, inst.arg, renv).toOption.flatMap {
                case (subst, Nil) => Some(subst(inst.ret))
                case (_, _ :: _) => None // if we have leftover constraints then it didn't actually unify
              }
          }
          simplifiedOpt match {
            // Can't reduce. Check what the original type was.
            case None =>
              t.baseType match {
                // If it's a var, it's ok. It may be substituted later to a type we can reduce.
                // Or it might be part of the signature as an associated type.
                case Type.Var(sym, loc) => Result.Ok((Type.AssocType(cst, t, kind, loc), p))
                // If it's an associated type, it's ok. It may be reduced later to a concrete type.
                case _: Type.AssocType => Result.Ok((Type.AssocType(cst, t, kind, loc), p))
                // Otherwise it's a problem.
                case baseTpe => Result.Err(ConstraintSolver.mkMissingInstance(cst.sym.trt, baseTpe, renv, loc))
              }
            // We could reduce! Simplify further if possible.
            case Some(t) => simplify(t, renv0, loc).map { case (res, _) => (res, true) }
          }
      }

    case Type.Alias(cst, args, t, _) => simplify(t, renv0, loc)
  }

  /**
   * Simplifies the type of the java method.
   *
   * @param tpe the type of the java method
   * @param loc the location where the java method has been called
   * @return
   */
  private def simplifyJava(tpe: Type, renv0: RigidityEnv, loc: SourceLocation): Result[(Type, Boolean), TypeError] = {
    tpe.typeConstructor match {
      case Some(TypeConstructor.MethodReturnType) =>
        val methodType = tpe.typeArguments.head
        methodType match {
          case Type.Cst(TypeConstructor.JvmMethod(method), _) => Result.Ok(Type.getFlixType(method.getReturnType), true)
          case _ => Result.Ok((tpe, false))
        }
      case _ => Result.Ok((tpe, false))
    }
  }

  /**
    * Returns `true` if the given type is still reducible, i.e. contains an unreduced MRT, e.g. MRT[a] where a is not known.
    */
  // TODO: This method should be recursive and not just look at the top-level type.
  def isReducible(tpe: Type): Boolean = tpe match {
    case Type.Apply(Type.Cst(TypeConstructor.MethodReturnType, _), Type.Var(_, _), _) => true
    case _ => false
  }

  /**
   * This is the resolution process of the Java constructor designated by a class and the parameter types.
   * Returns the return type of the Java constructor according, if there exists such a Java constructor.
   * Otherwise, either the Java constructor could not be found with the given signature or there was an ambiguity.
   *
   * @param clazz   the constructor's Java class
   * @param ts      the list containing the parameter types of the constructor
   * @param loc     the location where the java constructor has been invoked
   * @return        A JavaConstructorResolutionResult object that indicates the status of the resolution progress
   */
  def lookupConstructor(clazz: Class[_], ts: List[Type], renv: RigidityEnv, loc: SourceLocation): JavaConstructorResolutionResult = {
    retrieveConstructor(clazz, ts, renv, loc)
  }

  /**
   * This is the resolution process of the Java method method, member of the class of the Java object thisObj.
   * Returns the return type of the Java method according to the type of thisObj and the arguments of the method,
   * if there exists such a Java method.
   * Otherwise, either the Java method could not be found with the given method signature, or, there was an ambiguity.
   *
   * @param thisObj     the Java object
   * @param methodName  the Java method, supposedly member of the class of the Java object
   * @param ts          the list containing the type of thisObj and the arguments of the method
   * @param loc         the location where the Java method has been called
   * @return            A JavaMethodResolutionResult object that indicates the status of the resolution progress
   */
  def lookupMethod(thisObj: Type, methodName: String, ts: List[Type], renv: RigidityEnv, loc: SourceLocation): JavaMethodResolutionResult = {
    thisObj match { // there might be a possible factorization
      case Type.Cst(TypeConstructor.Str, _) =>
        val clazz = classOf[String]
        retrieveMethod(clazz, methodName, ts, loc = loc, renv = renv)

      case Type.Cst(TypeConstructor.BigInt, _) =>
        val clazz = classOf[BigInteger]
        retrieveMethod(clazz, methodName, ts, loc = loc, renv = renv)

      case Type.Cst(TypeConstructor.BigDecimal, _) =>
        val clazz = classOf[java.math.BigDecimal]
        retrieveMethod(clazz, methodName, ts, loc = loc, renv = renv)

      case Type.Cst(TypeConstructor.Regex, _) =>
        val clazz = classOf[java.util.regex.Pattern]
        retrieveMethod(clazz, methodName, ts, loc = loc, renv = renv)

      case Type.Cst(TypeConstructor.Native(clazz), _) =>
        retrieveMethod(clazz, methodName, ts, loc = loc, renv = renv)

      case _ => JavaMethodResolutionResult.MethodNotFound
    }
  }

  def lookupStaticMethod(clazz: Class[_], methodName: String, ts: List[Type], renv: RigidityEnv, loc: SourceLocation): JavaMethodResolutionResult = {
    retrieveMethod(clazz, methodName, ts, isStatic = true, loc = loc, renv = renv)
  }

  /**
   * Helper method to retrieve a constructor given its parameter types and the class.
   * Returns a JavaConstructorResolutionResult containing either the constructor, a list of candidate constructors or
   * a ConstructorNotFound object. The working process is similar to retrieveMethod and differs in the selection of candidate constructors.
   */
  private def retrieveConstructor(clazz: Class[_], ts: List[Type], renv: RigidityEnv, loc: SourceLocation): JavaConstructorResolutionResult = {
    val cands = candidateConstructors(clazz, ts, renv) match {
      case Some(v) => v
      case None => return JavaConstructorResolutionResult.UnresolvedTypes
    }

    cands.length match {
      case 0 => JavaConstructorResolutionResult.ConstructorNotFound
      case 1 =>
        val tpe = Type.Cst(TypeConstructor.JvmConstructor(cands.head), loc)
        JavaConstructorResolutionResult.Resolved(tpe)
      case _ =>
        // Among candidate constructors if there already exists the one with the exact signature,
        // we should ignore the rest.
        val exactConstructor = cands
          .filter(c => // Parameter types correspondence with subtyping
            (c.getParameterTypes zip ts).forall {
              case (clazz, tpe) => Type.getFlixType(clazz) == tpe
            })
        exactConstructor.length match {
          case 1 => JavaConstructorResolutionResult.Resolved(Type.Cst(TypeConstructor.JvmConstructor(exactConstructor.head), loc))
          case _ => JavaConstructorResolutionResult.AmbiguousConstructor(cands.toList) // 0 corresponds to no exact constructor, 2 or higher should be impossible in Java
        }
    }
  }

  /**
    * Returns `None` if there are unresolved types, otherwise
    * returns `Some` with the list of compatible constructors.
    */
  private def candidateConstructors(clazz: Class[_], ts: List[Type], renv: RigidityEnv): Option[List[Constructor[_]]] = {
    val constructors = clazz.getConstructors.toList
    val args = ts.length
    val ofLength = constructors.filter(_.getParameterCount == args)
    ofLength match {
      case Nil => Some(Nil)
      // TODO: this case can be added to enhance inference
      //       though it must be modified to handle varargs
      // case hd :: Nil => Some(List(hd))
      case multiple =>
        // track if isSubtypeOpt is missing type resolution
        var unresolvedTypes = false
        // zip is safe since we have already filtered on length
        val res = multiple.filter(cand => (cand.getParameterTypes zip ts).forall {
          case (clazz, tpe) => isSubtypeOpt(tpe, Type.getFlixType(clazz), renv) match {
            case None =>
              unresolvedTypes = true
              false
            case Some(b) => b
          }
        })
        // if some calls to getFlixTypeOpt is unresolved, we cant trust the list
        if (unresolvedTypes) None else Some(res)
    }
  }

  /**
   * Helper method to retrieve a method given its name and parameter types.
   * Returns a JavaMethodResolutionResult either containing the Java method or a MethodNotFound object.
   */
  private def retrieveMethod(clazz: Class[_], methodName: String, ts: List[Type], isStatic: Boolean = false, renv: RigidityEnv, loc: SourceLocation): JavaMethodResolutionResult = {
    // NB: this considers also static methods
    val candidateMethods = clazz.getMethods.filter(m => isCandidateMethod(m, methodName, isStatic, ts, renv))

    candidateMethods.length match {
      case 0 => JavaMethodResolutionResult.MethodNotFound
      case 1 =>
        val tpe = Type.Cst(TypeConstructor.JvmMethod(candidateMethods.head), loc)
        JavaMethodResolutionResult.Resolved(tpe)
      case _ =>
        // Among candidate methods if there already exists the method with the exact signature,
        // we should ignore the rest. E.g.: append(String), append(Object) in SB for the call append("a") should already know to use append(String)
        val exactMethod = candidateMethods
          .filter(m => // Parameter types correspondance with subtyping
            (m.getParameterTypes zip ts).forall {
              case (clazz, tpe) => Type.getFlixType(clazz) == tpe
            })
        exactMethod.length match {
          case 1 => JavaMethodResolutionResult.Resolved(Type.Cst(TypeConstructor.JvmMethod(exactMethod.head), loc))
          case _ => JavaMethodResolutionResult.AmbiguousMethod(candidateMethods.toList) // 0 corresponds to no exact method, 2 or higher should be impossible in Java
        }
    }
  }

  /**
   * Helper method that returns if the given method is a candidate method given a signature.
   *
   * @param cand       a candidate method
   * @param methodName the potential candidate method's name
   * @param ts         the list of parameter types of the potential candidate method
   */
  private def isCandidateMethod(cand: Method, methodName: String, isStatic: Boolean = false, ts: List[Type], renv: RigidityEnv): Boolean = {
    val static = java.lang.reflect.Modifier.isStatic(cand.getModifiers)
    (if (isStatic) static else !static) &&
      (cand.getName == methodName) &&
      (cand.getParameterCount == ts.length) &&
      // Parameter types correspondence with subtyping
      (cand.getParameterTypes zip ts).forall {
        case (clazz, tpe) => isSubtype(tpe, Type.getFlixType(clazz), renv)
      } &&
      // NB: once methods with same signatures have been filtered out, we should remove super-methods duplicates
      // if the superclass is abstract or ignore if it is a primitive type or void
      (cand.getReturnType.equals(Void.TYPE) || cand.getReturnType.isPrimitive || cand.getReturnType.isArray || // for all arrays return types?
        java.lang.reflect.Modifier.isInterface(cand.getReturnType.getModifiers) || // interfaces are considered primitives
        !(java.lang.reflect.Modifier.isAbstract(cand.getReturnType.getModifiers) && !isStatic))
  } // temporary to avoid superclass abstract duplicate, except for static methods

  /**
   * Helper method to define a sub-typing relation between two given Flix types.
   * Returns true if tpe1 is a sub-type of type tpe2, false otherwise.
   */
  @tailrec
  private def isSubtype(tpe1: Type, tpe2: Type, renv: RigidityEnv): Boolean = {
    (tpe1, tpe2) match {
      case (t1, t2) if t1 == t2 => true
      // Base types
      case (Type.Cst(TypeConstructor.Native(clazz1), _), Type.Cst(TypeConstructor.Native(clazz2), _)) => clazz2.isAssignableFrom(clazz1)
      case (Type.Cst(TypeConstructor.Unit, _), Type.Cst(TypeConstructor.Native(clazz), _)) if clazz == classOf[java.lang.Object] => true
      case (Type.Cst(TypeConstructor.Str, _), Type.Cst(TypeConstructor.Native(clazz), _)) => clazz.isAssignableFrom(classOf[java.lang.String])
      case (Type.Cst(TypeConstructor.BigInt, _), Type.Cst(TypeConstructor.Native(clazz), _)) => clazz.isAssignableFrom(classOf[java.math.BigInteger])
      case (Type.Cst(TypeConstructor.BigDecimal, _), Type.Cst(TypeConstructor.Native(clazz), _)) => clazz.isAssignableFrom(classOf[java.math.BigDecimal])
      case (Type.Cst(TypeConstructor.Regex, _), Type.Cst(TypeConstructor.Native(clazz), _)) => clazz.isAssignableFrom(classOf[java.util.regex.Pattern])
      // Arrays
      case (Type.Apply(Type.Apply(Type.Cst(TypeConstructor.Array, _), elmType1, _), _, _),
      Type.Apply(Type.Apply(Type.Cst(TypeConstructor.Array, _), elmType2, _), _, _)) =>
        isSubtype(elmType1, elmType2, renv)
      // Null is a sub-type of every Java object and non-primitive Flix type
      case (Type.Cst(TypeConstructor.Null, _), Type.Cst(TypeConstructor.Native(_), _)) => true
      // ignore alwaysNonPrimitive = None until fully using isSubtypeOpt
      case (Type.Cst(TypeConstructor.Null, _), tpe) =>
        val nonPrim = alwaysNonPrimitive(tpe, renv)
        nonPrim match {
          case Some(true) => true
          case Some(false) => false
          // this might crash - but it maintains current behaviour while transferring to isSubtypeOpt
          // specifically, returning false would mean that some calls with null would seem unambiguous
          case None => true
        }
      case _ => false
    }
  }

  /**
    * Helper method to define a sub-typing relation between two given Flix types.
    * Returns true if tpe1 is a sub-type of type tpe2, false otherwise.
    * Returns `None` if the types are too unresolved to decide.
    */
  @tailrec
  private def isSubtypeOpt(tpe1: Type, tpe2: Type, renv: RigidityEnv): Option[Boolean] = {
    (tpe1, tpe2) match {
      case (t1, t2) if t1 == t2 => Some(true)
      // Base types
      case (Type.Cst(TypeConstructor.Native(clazz1), _), Type.Cst(TypeConstructor.Native(clazz2), _)) =>
        Some(clazz2.isAssignableFrom(clazz1))
      case (Type.Cst(TypeConstructor.Unit, _), Type.Cst(TypeConstructor.Native(clazz), _)) if clazz == classOf[java.lang.Object] =>
        Some(true)
      case (Type.Cst(TypeConstructor.Str, _), Type.Cst(TypeConstructor.Native(clazz), _)) =>
        Some(clazz.isAssignableFrom(classOf[java.lang.String]))
      case (Type.Cst(TypeConstructor.BigInt, _), Type.Cst(TypeConstructor.Native(clazz), _)) =>
        Some(clazz.isAssignableFrom(classOf[java.math.BigInteger]))
      case (Type.Cst(TypeConstructor.BigDecimal, _), Type.Cst(TypeConstructor.Native(clazz), _)) =>
        Some(clazz.isAssignableFrom(classOf[java.math.BigDecimal]))
      case (Type.Cst(TypeConstructor.Regex, _), Type.Cst(TypeConstructor.Native(clazz), _)) =>
        Some(clazz.isAssignableFrom(classOf[java.util.regex.Pattern]))
      // Arrays
      case (Type.Apply(Type.Apply(Type.Cst(TypeConstructor.Array, _), elmType1, _), _, _),
      Type.Apply(Type.Apply(Type.Cst(TypeConstructor.Array, _), elmType2, _), _, _)) =>
        isSubtypeOpt(elmType1, elmType2, renv)
      // Null is a sub-type of every Java object and non-primitive Flix type
      case (Type.Cst(TypeConstructor.Null, _), Type.Cst(TypeConstructor.Native(_), _)) =>
        Some(true)
      case (Type.Cst(TypeConstructor.Null, _), tpe) =>
        alwaysNonPrimitive(tpe, renv)
      case _ if (tpe1.typeVars ++ tpe2.typeVars).forall(v => renv.isRigid(v.sym)(null)) => Some(false)
      case _ => None
    }
  }

  /**
    * Returns true iff the given type tpe is never a Flix primitive.
    * Returns `None` if the types are too unresolved to decide (e.g. accoc types).
    *
    *   - `alwaysNonPrimitive(a) = false`
    *   - `alwaysNonPrimitive(List[a]) = true`
    *   - `alwaysNonPrimitive(Int32) = false`
    */
  private def alwaysNonPrimitive(tpe: Type, renv: RigidityEnv): Option[Boolean] = {
    tpe match {
      case Type.Cst(TypeConstructor.Bool, _) => Some(false)
      case Type.Cst(TypeConstructor.Char, _) => Some(false)
      case Type.Cst(TypeConstructor.Float32, _) => Some(false)
      case Type.Cst(TypeConstructor.Float64, _) => Some(false)
      case Type.Cst(TypeConstructor.Int8, _) => Some(false)
      case Type.Cst(TypeConstructor.Int16, _) => Some(false)
      case Type.Cst(TypeConstructor.Int32, _) => Some(false)
      case Type.Cst(TypeConstructor.Int64, _) => Some(false)
      case Type.Cst(TypeConstructor.Str, _) => Some(true)
      case Type.Cst(TypeConstructor.Native(_), _) => Some(true)
      case Type.Cst(_, _) => Some(false) // TODO: more Some(true) and None cases in here
      case Type.Var(sym, _) =>
        // if sym is rigid we will never learn more (thus not always primitive)
        // if it is flexible we dont have enough information yet
        if (renv.isRigid(sym)(null)) Some(false) else None
      case Type.Alias(_, _, tpe, _) => alwaysNonPrimitive(tpe, renv)
      case Type.AssocType(_, _, _, _) =>
        // TODO: to be more precise we need to know if it could be simplified to type or not
        //       to sometimes return None
        Some(false)
      case Type.Apply(_, _, _) => Some(false) // TODO: more Some(true) and None cases in here
    }
  }

  /**
   * Represents the result of a resolution process of a java method.
   *
   * There are three possible outcomes:
   *
   *   1. Resolved(tpe): Indicates that there was some progress in the resolution and returns a
   *      simplified type of the java method.
   *   1. AmbiguousMethod: The resolution lacked some elements to find a java method among a set of
   *      methods.
   *   1. MethodNotFound(): The resolution failed to find a corresponding java method.
   */
  sealed trait JavaMethodResolutionResult
  object JavaMethodResolutionResult {
    case class Resolved(tpe: Type) extends JavaMethodResolutionResult
    case class AmbiguousMethod(methods: List[Method]) extends JavaMethodResolutionResult
    case object MethodNotFound extends JavaMethodResolutionResult
  }

  /**
   * Represents the result of a resolution process of a java constructor.
   *
   * There are three possible outcomes:
   *   1. Resolved(tpe): Indicates that there was some progress in the resolution and returns a simplified type of the java constructor.
   *   1. AmbiguousConstructor: The resolution lacked some elements to find a java constructor among a set of constructors.
   *   1. ConstructorNotFound(): The resolution failed to find a corresponding java constructor.
   */
  sealed trait JavaConstructorResolutionResult
  object JavaConstructorResolutionResult {
    case class Resolved(tpe: Type) extends JavaConstructorResolutionResult
    case class AmbiguousConstructor(constructors: List[Constructor[_]]) extends JavaConstructorResolutionResult
    case object ConstructorNotFound extends JavaConstructorResolutionResult
    case object UnresolvedTypes extends JavaConstructorResolutionResult
  }
}
