/*
 *  Copyright 2024 Jonathan Lindegaard Starup
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *  http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */

package ca.uwaterloo.flix.language.phase

import ca.uwaterloo.flix.language.ast.{SourceLocation, Type, TypeConstructor}
import ca.uwaterloo.flix.util.InternalCompilerException

import java.lang.reflect.{Field, Member, Method}

object Jvm {


  /**
    * Returns the (static/dynamic) `fieldName` field of `clazz` if it exists.
    *
    * Field name "length" of array classes always return `None` (see Class.getField).
    *
    * @param clazz the class to search
    * @param static whether to find a static field or an instance field
    */
  def getField(clazz: Class[?], fieldName: String, static: Boolean): Option[Field] = {
    try {
      val field = clazz.getField(fieldName)
      if (isStatic(field) == static) Some(field) else None
    } catch {
      case _: NoSuchFieldException => None
    }
  }

  /** Returns `true` if `member` is a static member ([[Field]] and [[Method]] extends [[Member]]). */
  def isStatic(member: Member): Boolean =
    java.lang.reflect.Modifier.isStatic(member.getModifiers)

  /** Returns `true` if `member` is an instance member ([[Field]] and [[Method]] extends [[Member]]). */
  def isInstance(member: Member): Boolean =
    !isStatic(member)

  /**
    * Returns the methods of the class.
    *
    * If the given class is an array, the method `clone` is not included (see Class.getMethods).
    *
    * Returns `Nil` if both static` and `instance` is `false`.
    *
    * @param clazz the class to search
    * @param static whether to include static methods
    * @param instance whether to include instance methods
    */
  def getMethodsHelper(clazz: Class[?], static: Boolean, instance: Boolean): List[Method] = {
    val allMethods = clazz.getMethods.toList
    var methods = allMethods

    // We have to add the methods from Object manually for interfaces (see Class.getMethods).
    // Object only has instance methods, so skip if those are not relevant.
    if (instance && clazz.isInterface) {
      // If interface has `boolean eq(that: Object)` we should omit `Object.eq`
      // If interface I has `boolean eq(that: I)` we should include `Object.eq`
      val objectMethods = classOf[Object].getMethods.toList
      val undeclaredObjectMethods = objectMethods.filter {
        objectMethod => !allMethods.exists(methodsMatch(objectMethod, _))
      }
      methods = methods ::: undeclaredObjectMethods
    }

    // Remove static methods if not wanted.
    if (!static) methods = methods.filterNot(isStatic(_))
    // Remove instance methods if not wanted.
    if (!instance) methods = methods.filterNot(isInstance(_))
    methods
  }

  /**
    * Returns the methods of the class.
    *
    * If the given class is an array, the method `clone` is not included (see Class.getMethods).
    */
  def getMethods(clazz: Class[?]): List[Method] =
    getMethodsHelper(clazz, static = true, instance = true)

  /**
    * Returns the static methods of the class.
    */
  def getStaticMethods(clazz: Class[?]): List[Method] =
    getMethodsHelper(clazz, static = true, instance = false)

  /**
    * Returns the instance methods of the class.
    *
    * If the given class is an array, the method `clone` is not included (see Class.getMethods).
    */
  def getInstanceMethods(clazz: Class[?]): List[Method] =
    getMethodsHelper(clazz, static = false, instance = true)

  /** Returns true if the methods are the same in regards to overloading. */
  private def methodsMatch(m1: Method, m2: Method): Boolean = {
    m1.getName == m2.getName &&
      Jvm.isStatic(m1) == Jvm.isStatic(m2) &&
      m1.getParameterTypes.sameElements(m2.getParameterTypes)
  }

  //
  // Flix type and JVM type conversions.
  //

  /**
    * Returns the [[Class]] of `tpe` if any.
    *
    *   - `getExactClass(String) = java.lang.String`
    *   - `getExactClass(Native(java.util.List)) = java.util.List`
    *   - `getExactClass(Unit) = None`
    *   - `getExactClass(Array[Int32, r]) = []int`
    *   - `getExactClass(Array[Unit, r]) = None`
    *   - `getExactClass(Array[Unit, r], lenientArrays = true) = []Object`
    *   - `getExactClass(Array[Array[Unit, IO], r]) = None`
    *   - `getExactClass(Array[Array[Unit, IO], r], lenientArrays = true) = [][]Object`
    *
    * @param lenientArrays if `true`, arrays of unknown types will be object arrays.
    */
  def getExactClass(tpe: Type, lenientArrays: Boolean = false): Option[Class[?]] = tpe match {
    case Type.Cst(tc, _) => tc match {
      case TypeConstructor.Bool => Some(java.lang.Boolean.TYPE)
      case TypeConstructor.Char => Some(java.lang.Character.TYPE)
      case TypeConstructor.Float32 => Some(java.lang.Float.TYPE)
      case TypeConstructor.Float64 => Some(java.lang.Double.TYPE)
      case TypeConstructor.BigDecimal => Some(classOf[java.math.BigDecimal])
      case TypeConstructor.Int8 => Some(java.lang.Byte.TYPE)
      case TypeConstructor.Int16 => Some(java.lang.Short.TYPE)
      case TypeConstructor.Int32 => Some(java.lang.Integer.TYPE)
      case TypeConstructor.Int64 => Some(java.lang.Long.TYPE)
      case TypeConstructor.BigInt => Some(classOf[java.math.BigInteger])
      case TypeConstructor.Str => Some(classOf[java.lang.String])
      case TypeConstructor.Regex => Some(classOf[java.util.regex.Pattern])
      // TODO arrow?
      case TypeConstructor.Native(clazz) => Some(clazz)
      case _ => None
    }
    case Type.Apply(Type.Apply(Type.Cst(TypeConstructor.Array, _), elm, _), _, _) =>
      getExactClass(elm) match {
        case Some(elmClass) => Some(arrayOf(elmClass))
        case None => if (lenientArrays) Some(arrayOf(classOf[Object])) else None
      }
    case _ => None
  }

  /**
    * Returns the [[Type]] of `clazz`.
    *
    * Arrays are returned in `reg`.
    *
    * Functions are not converted to Java function interfaces since that is unsound.
    */
  def getType(clazz: Class[?], reg: Type, loc: SourceLocation): Type = {
    if (clazz == java.lang.Boolean.TYPE) Type.mkBool(loc)
    else if (clazz == java.lang.Character.TYPE) Type.mkChar(loc)
    else if (clazz == java.lang.Float.TYPE) Type.mkFloat32(loc)
    else if (clazz == java.lang.Double.TYPE) Type.mkFloat64(loc)
    else if (clazz == classOf[java.math.BigDecimal]) Type.mkBigDecimal(loc)
    else if (clazz == java.lang.Byte.TYPE) Type.mkInt8(loc)
    else if (clazz == java.lang.Short.TYPE) Type.mkInt16(loc)
    else if (clazz == java.lang.Integer.TYPE) Type.mkInt32(loc)
    else if (clazz == java.lang.Long.TYPE) Type.mkInt64(loc)
    else if (clazz == classOf[java.math.BigInteger]) Type.mkBigInt(loc)
    else if (clazz == classOf[java.lang.String]) Type.mkString(loc)
    else if (clazz == classOf[java.util.regex.Pattern]) Type.mkRegex(loc)
    else if (clazz.isArray) {
      val elm = getArrayElementType(clazz, loc)
      Type.mkArray(getType(elm, reg, loc), reg, loc)
    } else Type.mkNative(clazz, loc)
  }

  /**
    * Returns the [[Type]] of `clazz` or [[TypeConstructor.Unit]] if `clazz` is void.
    *
    * Arrays are returned in `reg`.
    *
    * Functions are not converted to Java function interfaces since that is unsound.
    */
  def getTypeWithVoid(clazz: Class[?], reg: Type, loc: SourceLocation): Type = {
    if (clazz == java.lang.Void.TYPE) Type.mkUnit(loc)
    else getType(clazz, reg, loc)
  }

  /** Returns the element type of the given array Class.
    *
    * Throws [[InternalCompilerException]] if `clazz` is not an array class.
    */
  private def getArrayElementType(clazz: Class[?], loc: SourceLocation): Class[?] = {
    val res = clazz.getComponentType
    if (res == null) throw InternalCompilerException("Unexpected non-array class", loc)
    else res
  }

  def arrayOf[T](clazz: Class[T]): Class[?] =
    java.lang.reflect.Array.newInstance(clazz, 0).getClass

}
