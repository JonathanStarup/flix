namespace Test/Dec/TypeAlias {

    /**
     * A type alias for degrees celsius.
     */
    type alias Celsius = Int

    /**
     * A type alias for degrees fahrenheit.
     */
    type alias Fahrenheit = Int

    /**
     * A type alias for united states dollars.
     */
    type alias USD = Float64

    /**
     * A type alias for canadian dollars.
     */
    type alias CAD = Float64

    /**
     * A type alias for Option of Int.
     */
    type alias A = Option[Int]

    /**
     * A type alias for a Result.
     */
    type alias B = Result[Bool, Int]

    /**
     * A polymorphic type alias for a Option.
     */
    type alias C[a] = Option[a]

    /**
     * A polymorphic type alias for a Result.
     */
    type alias D[a, b] = Result[a, b]

    /**
     * A partially polymorphic type alias for a Result.
     */
    type alias E[a] = Result[a, String]

    @test
    def testTypeAlias01(): Celsius = 123

    @test
    def testTypeAlias02(): Fahrenheit = 123

    @test
    def testTypeAlias03(): Int = (123: Celsius) + (123: Fahrenheit)

    @test
    def testTypeAlias04(): USD = 123.456

    @test
    def testTypeAlias05(): CAD = 123.456

    @test
    def testTypeAlias06(): Float64 = (123.456: USD) + (123.456: CAD)

    @test
    def testTypeAlias07(): A = None

    @test
    def testTypeAlias08(): A = Some(123)

    @test
    def testTypeAlias09(): B = Ok(true)

    @test
    def testTypeAlias10(): B = Err(123)

    @test
    def testTypeAlias11(): C[Bool] = None

    @test
    def testTypeAlias12(): C[Bool] = Some(true)

    @test
    def testTypeAlias13(): C[Int] = None

    @test
    def testTypeAlias14(): C[Int] = Some(123)

    @test
    def testTypeAlias15(): D[Bool, Int] = Ok(true)

    @test
    def testTypeAlias16(): D[Bool, Int] = Err(123)

    @test
    def testTypeAlias17(): E[Bool] = Ok(true)

    @test
    def testTypeAlias18(): E[Int] = Ok(123)

    @test
    def testTypeAlias19(): E[Bool] = Err("Hello World")

    @test
    def testTypeAlias20(): E[Int] = Err("Hello World")

    /**
     * An opaque type for Int.
     */
    opaque type X = Int

    /**
     * An opaque type for Option.
     */
    opaque type Y[a] = Option[a]

    /**
     * An opaque type for Result.
     */
    opaque type Z[a, b] = Result[a, b]

    /**
     * A type alias for an opaque type.
     */
    type alias U = X

    /**
     * A type alias for a polymorphic opaque type.
     */
    type alias V[a] = Y[a]

    /**
     * A type alias for a polymorphic opaque type.
     */
    type alias W[a, b] = Z[a, b]

    @test
    def testTypeAlias21(): U = X(123)

    @test
    def testTypeAlias22(): V[Bool] = Y(None)

    @test
    def testTypeAlias23(): V[Bool] = Y(Some(true))

    @test
    def testTypeAlias24(): V[Int] = Y(None)

    @test
    def testTypeAlias25(): V[Int] = Y(Some(123))

    @test
    def testTypeAlias26(): W[Bool, Int] = Z(Ok(true))

    @test
    def testTypeAlias27(): W[Bool, Int] = Z(Err(123))

    enum Option[t] {
        case None,
        case Some(t)
    }

    enum Result[t, e] {
        case Ok(t),
        case Err(e)
    }

}
