/*
 * Copyright 2025 Jonathan Lindegaard Starup
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

package ca.uwaterloo.flix.language.ast

import ca.uwaterloo.flix.language.phase.jvm.BackendType

object LowLevelAst {

  case class Root(defs: Map[Symbol.DefnSym, Def])

  sealed trait Def

  case class DirectDef(sym: Symbol.DefnSym, fparams: List[FormalParam], expr: Expr, tpe: BackendType, loc: SourceLocation) extends Def

  case class EffectDef(sym: Symbol.EffectSym, fparams: List[FormalParam])

  case class FormalParam(offset: Int, tpe: BackendType, loc: SourceLocation)

  sealed trait Expr

}

