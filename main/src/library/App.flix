/*
 *  Copyright 2024 Magnus Madsen
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
mod App {

    ///
    /// Runs the given function `f` handling all effects specified in the signature.
    ///
    pub def runAll(f: Unit -> a \ ef): a \ (ef - {Clock, Console, FileReadWithResult, FileWriteWithResult, Http, Logger}) + {IO, Net} =
        let r = f |>
            Clock.handle |>
            Console.handle |>
            FileReadWithResult.handle |>
            FileWriteWithResult.handle |>
            Logger.handle |>
            Http.handle;
        r()

    ///
    /// Runs the given function `f` handling all effects specified in the signature where some handlers may return `Result`.
    ///
    pub def runAllWithResult(f: Unit -> a \ ef): Result[IoError, a] \ (ef - {Clock, Console, FileRead, FileWrite, Http, Logger}) + {IO, Net} =
        let r1 = Clock.handle >> Console.handle >> Logger.handle >> Http.handle;
        let r2 = (FileWrite.handle >> FileRead.handle >> (g -> g >> Result.flatten));
        (f |> (r1 >> r2))()
}
