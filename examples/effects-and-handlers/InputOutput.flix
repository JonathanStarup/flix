mod InputOutputExample {

    import java.lang.System

    eff InputOutput {
        def read(): String
        def write(s: String): Unit
    }

    pub def main(): Result[String, Unit] \ IO = {

        println("");
        println("First with hardcoded input:");
        run helloExample() with InputOutput {
            def read(k) = k("Alice")
            def write(s, k) = {println(s); k()}
        };

        println("");
        println("Then with actual console interaction:");
        runWithConsole(helloExample)
    }

    def runWithConsole(f: Unit -> t \ ef + InputOutput): Result[String, t] \ ef + IO = {
        run Ok(f()) with InputOutput {
            def read(k) = k(System.console().readLine())
            def write(s, k) = {println(s); k()}
        }
    }


    pub def helloExample(): Unit \ InputOutput = {
        InputOutput.write("What is your name?");
        let name = InputOutput.read();
        InputOutput.write("Hello ${name}!")
    }

}
