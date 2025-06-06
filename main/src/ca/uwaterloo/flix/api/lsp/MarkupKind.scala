/*
 * Copyright 2020 Magnus Madsen
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
package ca.uwaterloo.flix.api.lsp

import org.eclipse.lsp4j
import org.json4s.JString
import org.json4s.JsonAST.JValue

/**
  * Represents a `MarkupKind` in LSP.
  */
sealed trait MarkupKind {
  def toJSON: JValue = this match {
    case MarkupKind.PlainText => JString("plaintext")
    case MarkupKind.Markdown => JString("markdown")
  }

  def toLsp4j: String = this match {
    case MarkupKind.PlainText => lsp4j.MarkupKind.PLAINTEXT
    case MarkupKind.Markdown => lsp4j.MarkupKind.MARKDOWN
  }
}

object MarkupKind {

  case object PlainText extends MarkupKind

  case object Markdown extends MarkupKind

}
