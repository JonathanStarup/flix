namespace Test/Exp/Reference/Precedence {

    @test
    def testRefPrecedence01(): Bool & Impure =
        let l = ref ref 123;
        let r = deref deref l;
        r == 123

    @test
    def testRefPrecedence02(): Bool & Impure =
        let l = ref ref ref 123;
        let r = deref deref deref l;
        r == 123

    @test
    def testRefPrecedence03(): Bool & Impure =
        let x = ref 123;
        let y = ref 123;
        let r = deref x + deref y;
        r == (123 + 123)

}
