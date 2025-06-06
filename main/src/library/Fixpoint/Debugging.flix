/*
 * Copyright 2021 Magnus Madsen
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

mod Fixpoint.Debugging {

    use Fixpoint.Ast.Datalog.Datalog
    use Fixpoint.Ast.Ram.RamStmt
    use Fixpoint.Ast.Shared.PredSym

    ///
    /// Invoked before the fixpoint computation.
    ///
    /// Note: Returns `d` to ensure it is not erased.
    ///
    @Internal
    pub def notifyPreSolve(d: Datalog): Datalog = unchecked_cast({
        if (Fixpoint.Options.enableDebugging()) {
            println(String.repeat(80, "*"));
            println("** Datalog Input");
            println(String.repeat(80, "*"));
            println("");
            println(String.indent(4, "${d}"));
            println("");
            d
        } else {
            d
        }
    } as _ \ {})

    ///
    /// Invoked with the minimal model of the fixpoint computation.
    ///
    /// Note: Returns `d` to ensure it is not erased.
    ///
    @Internal
    pub def notifyPostSolve(d: Datalog): Datalog = unchecked_cast({
        if (Fixpoint.Options.enableDebugging()) {
            println(String.repeat(80, "*"));
            println("** Minimal Model");
            println(String.repeat(80, "*"));
            println("");
            println(String.indent(4, "${d}"));
            println("");
            d
        } else {
            d
        }
    } as _ \ {})

    ///
    /// Invoked before the fixpoint computation.
    ///
    /// Note: Returns `s` to ensure it is not erased.
    ///
    @Internal
    pub def notifyPreInterpret(s: RamStmt): RamStmt = unchecked_cast({
        if (Fixpoint.Options.enableDebugging()) {
            println(String.repeat(80, "*"));
            println("** Relation Algebra Machine AST");
            println(String.repeat(80, "*"));
            println("");
            println(String.indent(4, "${s}"));
            println("");
            s
        } else {
            s
        }
    } as _ \ {})

}
