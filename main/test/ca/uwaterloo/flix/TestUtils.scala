/*
 * Copyright 2016 Magnus Madsen
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

package ca.uwaterloo.flix

import ca.uwaterloo.flix.api.Flix
import ca.uwaterloo.flix.language.CompilationMessage
import ca.uwaterloo.flix.language.ast.shared.SecurityContext
import ca.uwaterloo.flix.language.ast.{SourceLocation, TypedAst}
import ca.uwaterloo.flix.runtime.CompilationResult
import ca.uwaterloo.flix.util.collection.Chain
import ca.uwaterloo.flix.util.{Formatter, Options, Result, Validation}
import org.scalatest.funsuite.AnyFunSuite

import scala.reflect.ClassTag

trait TestUtils {

  this: AnyFunSuite =>

  /**
    * Checks the given input string `s` with the given compilation options `o`.
    */
  def check(s: String, o: Options): (Option[TypedAst.Root], List[CompilationMessage]) = {
    implicit val sctx: SecurityContext = SecurityContext.AllPermissions
    new Flix().setOptions(o).addSourceCode("<test>", s).check()
  }

  /**
    * Compiles the given input string `s` with the given compilation options `o`.
    */
  def compile(s: String, o: Options): Validation[CompilationResult, CompilationMessage] = {
    implicit val sctx: SecurityContext = SecurityContext.AllPermissions
    new Flix().setOptions(o).addSourceCode("<test>", s).compile()
  }

  private def errorString(errors: Seq[CompilationMessage]): String = {
    errors.map(_.messageWithLoc(Formatter.NoFormatter)).mkString("\n\n")
  }

  /**
    * Asserts that the result of a compiler check is a failure with a value of the parametric type `T`.
    */
  def expectErrorOnCheck[T](result: (Option[TypedAst.Root], List[CompilationMessage]))(implicit classTag: ClassTag[T]): Unit = result match {
    case (Some(root), Nil) => expectErrorGen[TypedAst.Root, T](Validation.Success(root))
    case (_, errors) => expectErrorGen[TypedAst.Root, T](Validation.Failure(Chain.from(errors)))
  }

  /**
    * Asserts that the compilation result is a failure with a value of the parametric type `T`.
    */
  def expectError[T](result: Validation[CompilationResult, CompilationMessage], allowUnknown: Boolean = false)(implicit classTag: ClassTag[T]): Unit = expectErrorGen[CompilationResult, T](result, allowUnknown)

  /**
    * Asserts that validation contains a defined entry point.
    */
  def expectMain(result: (Option[TypedAst.Root], List[CompilationMessage])): Unit = result match {
    case (Some(root), _) =>
      if (root.mainEntryPoint.isEmpty) {
        fail("Expected 'main' to be defined.")
      }
    case _ => fail("Expected 'main' to be defined.")
  }

  /**
    * Asserts that the validation does not contain a value of the parametric type `T`.
    */
  def rejectError[T](result: Validation[CompilationResult, CompilationMessage])(implicit classTag: ClassTag[T]): Unit = result.toResult match {
    case Result.Ok(_) => ()

    case Result.Err(errors) =>
      val rejected = classTag.runtimeClass
      val actuals = errors.map(_.getClass)

      if (actuals.exists(rejected.isAssignableFrom(_)))
        fail(s"Unexpected an error of type ${rejected.getSimpleName}.")
  }

  /**
    * Asserts that the validation is successful.
    */
  def expectSuccess(result: Validation[CompilationResult, CompilationMessage]): Unit = result.toResult match {
    case Result.Ok(_) => ()
    case Result.Err(errors) =>
      fail(s"Expected success, but found errors:\n\n${errorString(errors.toSeq)}.")
  }

  /**
    * Private generic version of expectError.
    * Asserts that the validation is a failure with a value of the parametric type `T`.
    */
  private def expectErrorGen[R, T](result: Validation[R, CompilationMessage], allowUnknown: Boolean = false)(implicit classTag: ClassTag[T]): Unit = result.toResult match {
    case Result.Ok(_) => fail(s"Expected Failure, but got Success.")

    case Result.Err(errors) =>
      val expected = classTag.runtimeClass

      // Get the expected error line from the first error
      // It doesn't matter which error we use because we just need the source code
      val expectedLine = getExpectedErrorLine(errors.head.get)
      val actuals = errors.map(e => (e, e.getClass)).toList
      actuals.find {
        case (message, actualClazz) => expected.isAssignableFrom(actualClazz) && expectedLine.forall(isOnLine(message, _))
      } match {
        case Some((actual, _)) =>
          // Require known source location only on the expected error.
          if (actual.loc == SourceLocation.Unknown) {
            if (!allowUnknown) fail("Error contains unknown source location.")
          }

        case None =>
          val onLineString = expectedLine match {
            case None => ""
            case Some(line) => s" on line $line"
          }
          fail(s"Expected an error of type ${expected.getSimpleName}${onLineString}, but found:\n\n${actuals.map(p => p._2.getName)}.")
      }
  }

  /**
    * Returns the one-indexed line where the error is expected, if specified.
    */
  private def getExpectedErrorLine(error: CompilationMessage): Option[Int] = {
    val content = new String(error.source.data)
    val expectedIndex = content.linesIterator.indexWhere(_.contains("ERROR"))

    // expectedIndex is -1 if no line contains ERROR
    // line numbers are offset by 1
    expectedIndex match {
      case -1 => None
      case index => Some(index + 1)
    }
  }

  /**
    * Returns true if the compilation message is ONLY on the given line (one-indexed).
    */
  private def isOnLine(error: CompilationMessage, line: Int) = {
    error.loc.sp1.lineOneIndexed == line && error.loc.sp2.lineOneIndexed == line
  }
}
