package ca.uwaterloo.flix

import ca.uwaterloo.flix.api.Flix
import ca.uwaterloo.flix.language.ast.Symbol
import ca.uwaterloo.flix.runtime.{Model, Value}
import ca.uwaterloo.flix.util.{DebugBytecode, _}
import org.scalatest.FunSuite

class TestExamples extends FunSuite {

  private class Tester(dumpBytecode: Boolean = false) {

    private val interpretedFlix = createFlix(codegen = false)
    private val compiledFlix = createFlix(codegen = true)
    private var interpreted: Model = null
    private var compiled: Model = null

    private def createFlix(codegen: Boolean = false) = {
      val options = Options(
        debugger = Debugger.Disabled,
        print = Nil,
        verbosity = Verbosity.Silent,
        verify = Verify.Disabled,
        codegen = if (codegen) CodeGeneration.Enabled else CodeGeneration.Disabled,
        debugBytecode = if (dumpBytecode) DebugBytecode.Enabled else DebugBytecode.Disabled
      )
      new Flix().setOptions(options)
    }

    def addPath(path: String): Tester = {
      interpretedFlix.addPath(path)
      compiledFlix.addPath(path)
      this
    }

    def addStr(str: String): Tester = {
      interpretedFlix.addStr(str)
      compiledFlix.addStr(str)
      this
    }

    def run(): Tester = {
      interpreted = interpretedFlix.solve().get
      compiled = compiledFlix.solve().get
      this
    }

    def checkValue(expected: AnyRef, latticeName: String, key: List[AnyRef]): Unit = {
      withClue(s"interpreted value $latticeName($key):") {
        val lattice = interpreted.getLattice(latticeName).toMap
        assertResult(expected)(lattice(key))
      }
      withClue(s"compiled value $latticeName($key):") {
        val lattice = compiled.getLattice(latticeName).toMap
        assertResult(expected)(lattice(key))
      }
    }

    def checkNone(latticeName: String, key: List[AnyRef]): Unit = {
      withClue(s"interpreted value $latticeName($key):") {
        val lattice = interpreted.getLattice(latticeName).toMap
        assertResult(None)(lattice.get(key))
      }
      withClue(s"compiled value $latticeName($key):") {
        val lattice = compiled.getLattice(latticeName).toMap
        assertResult(None)(lattice.get(key))
      }
    }

    def checkSuccess(): Unit = {
      assert(interpretedFlix.solve().isSuccess)
      assert(compiledFlix.solve().isSuccess)
    }

  }

  /////////////////////////////////////////////////////////////////////////////
  // Domains                                                                 //
  /////////////////////////////////////////////////////////////////////////////

  test("Belnap.flix") {
    val input =
      """namespace Belnap {
        |    let Belnap<> = (Belnap.Bot, Belnap.Top, leq, lub, glb);
        |    lat A(k: Int, v: Belnap);
        |
        |    A(1, Belnap.True).
        |    A(2, Belnap.False).
        |
        |    A(3, Belnap.True).
        |    A(3, Belnap.False).
        |
        |    A(4, x) :- A(1, x), A(2, x).
        |
        |    A(5, not(Belnap.False)).
        |
        |    A(6, and(Belnap.True, Belnap.False)).
        |
        |    A(7, or(Belnap.True, Belnap.False)).
        |
        |    A(8, xor(Belnap.True, Belnap.False)).
        |}
      """.stripMargin

    val t = new Tester()
      .addPath("./examples/domains/Belnap.flix")
      .addStr(input)
      .run()

    val Belnap = Symbol.Resolved.mk(List("Belnap", "Belnap"))

    val Tru = Value.mkTag(Belnap, "True", Value.Unit)
    val Fls = Value.mkTag(Belnap, "False", Value.Unit)
    val Top = Value.mkTag(Belnap, "Top", Value.Unit)

    t.checkValue(List(Tru), "Belnap/A", List(Value.mkInt32(1)))
    t.checkValue(List(Fls), "Belnap/A", List(Value.mkInt32(2)))
    t.checkValue(List(Top), "Belnap/A", List(Value.mkInt32(3)))
    t.checkNone("Belnap/A", List(Value.mkInt32(4)))
    t.checkValue(List(Tru), "Belnap/A", List(Value.mkInt32(5)))
    t.checkValue(List(Fls), "Belnap/A", List(Value.mkInt32(6)))
    t.checkValue(List(Tru), "Belnap/A", List(Value.mkInt32(7)))
    t.checkValue(List(Tru), "Belnap/A", List(Value.mkInt32(8)))
  }

  test("Constant.flix") {
    val input =
      """namespace Constant {
        |    let Constant<> = (Constant.Bot, Constant.Top, leq, lub, glb);
        |    lat A(k: Int, v: Constant);
        |
        |    A(0, Constant.Cst(0)).
        |    A(1, Constant.Cst(1)).
        |    A(2, Constant.Cst(2)).
        |
        |    A(3, x) :- A(0, x).
        |    A(3, x) :- A(1, x).
        |    A(3, x) :- A(2, x).
        |
        |    A(4, x) :- A(0, x), A(1, x), A(2, x).
        |
        |    A(5, plus(x, y))  :- A(0, x), A(2, y).
        |    A(6, times(x, y)) :- A(1, x), A(2, y).
        |}
      """.stripMargin

    val t = new Tester()
      .addPath("./examples/domains/Belnap.flix")
      .addPath("./examples/domains/Constant.flix")
      .addStr(input)
      .run()

    val Constant = Symbol.Resolved.mk(List("Constant", "Constant"))

    val Zer = Value.mkTag(Constant, "Cst", Value.mkInt32(0))
    val One = Value.mkTag(Constant, "Cst", Value.mkInt32(1))
    val Two = Value.mkTag(Constant, "Cst", Value.mkInt32(2))
    val Top = Value.mkTag(Constant, "Top", Value.Unit)

    t.checkValue(List(Zer), "Constant/A", List(Value.mkInt32(0)))
    t.checkValue(List(One), "Constant/A", List(Value.mkInt32(1)))
    t.checkValue(List(Two), "Constant/A", List(Value.mkInt32(2)))
    t.checkValue(List(Top), "Constant/A", List(Value.mkInt32(3)))
    t.checkNone("Constant/A", List(Value.mkInt32(4)))
    t.checkValue(List(Two), "Constant/A", List(Value.mkInt32(5)))
    t.checkValue(List(Two), "Constant/A", List(Value.mkInt32(6)))
  }

  // TODO: Implement BigInt in interpreter and codegen
  ignore("ConstantSign.flix") {
    val input =
      """namespace ConstantSign {
        |    let ConstSign<> = (ConstSign.Bot, ConstSign.Top, leq, lub, glb);
        |    lat A(k: Int, v: ConstSign);
        |
        |    A(1, ConstSign.Cst(-1ii)).
        |    A(2, ConstSign.Cst(0ii)).
        |    A(3, ConstSign.Cst(1ii)).
        |
        |    A(4, x) :- A(1, x). // 4 -> top
        |    A(4, x) :- A(2, x). // 4 -> top
        |    A(4, x) :- A(3, x). // 4 -> top
        |
        |    A(5, x) :- A(2, x). // 5 -> pos
        |    A(5, x) :- A(3, x). // 5 -> pos
        |
        |    A(6, x) :- A(1, x), A(2, x). // 6 -> bot
        |    A(7, x) :- A(2, x), A(3, x). // 7 -> bot
        |
        |    A(8, x) :- A(4, x), A(5, x). // 8 -> pos
        |
        |    A(9, times(x, y)) :- A(1, x), A(1, y). // 9 -> 1
        |}
      """.stripMargin

    val t = new Tester()
      .addPath("./examples/domains/Belnap.flix")
      .addPath("./examples/domains/ConstantSign.flix")
      .addStr(input)
      .run()

    val ConstantSign = Symbol.Resolved.mk(List("ConstantSign", "ConstSign"))

    val Zer = Value.mkTag(ConstantSign, "Cst", Value.mkInt32(0))
    val One = Value.mkTag(ConstantSign, "Cst", Value.mkInt32(1))
    val Pos = Value.mkTag(ConstantSign, "Pos", Value.Unit)
    val Top = Value.mkTag(ConstantSign, "Top", Value.Unit)

    t.checkValue(List(Zer), "ConstantSign/A", List(Value.mkInt32(2)))
    t.checkValue(List(One), "ConstantSign/A", List(Value.mkInt32(3)))
    t.checkValue(List(Top), "ConstantSign/A", List(Value.mkInt32(4)))
    t.checkValue(List(Top), "ConstantSign/A", List(Value.mkInt32(4)))
    t.checkValue(List(Pos), "ConstantSign/A", List(Value.mkInt32(5)))
    t.checkNone("ConstantSign/A", List(Value.mkInt32(6)))
    t.checkNone("ConstantSign/A", List(Value.mkInt32(7)))
    t.checkValue(List(Pos), "ConstantSign/A", List(Value.mkInt32(8)))
    t.checkValue(List(One), "ConstantSign/A", List(Value.mkInt32(9)))
  }

  test("Parity.flix") {
    val input =
      """namespace Parity {
        |    let Parity<> = (Parity.Bot, Parity.Top, leq, lub, glb);
        |    lat A(k: Int, v: Parity);
        |
        |    A(1, Parity.Odd).
        |    A(2, Parity.Even).
        |
        |    A(3, Parity.Odd).
        |    A(3, Parity.Even).
        |
        |    A(4, x) :- A(1, x), A(2, x).
        |
        |    A(5, plus(Parity.Odd, Parity.Even)).
        |
        |    A(6, plus(Parity.Odd, Parity.Odd)).
        |
        |    A(7, times(Parity.Odd, Parity.Even)).
        |
        |    A(8, times(Parity.Odd, Parity.Odd)).
        |}
      """.stripMargin

    val t = new Tester()
      .addPath("./examples/domains/Belnap.flix")
      .addPath("./examples/domains/Parity.flix")
      .addStr(input)
      .run()

    val Parity = Symbol.Resolved.mk(List("Parity", "Parity"))

    val Odd = Value.mkTag(Parity, "Odd", Value.Unit)
    val Evn = Value.mkTag(Parity, "Even", Value.Unit)
    val Top = Value.mkTag(Parity, "Top", Value.Unit)

    t.checkValue(List(Odd), "Parity/A", List(Value.mkInt32(1)))
    t.checkValue(List(Evn), "Parity/A", List(Value.mkInt32(2)))
    t.checkValue(List(Top), "Parity/A", List(Value.mkInt32(3)))
    t.checkNone("Parity/A", List(Value.mkInt32(4)))
    t.checkValue(List(Odd), "Parity/A", List(Value.mkInt32(5)))
    t.checkValue(List(Evn), "Parity/A", List(Value.mkInt32(6)))
    t.checkValue(List(Evn), "Parity/A", List(Value.mkInt32(7)))
    t.checkValue(List(Odd), "Parity/A", List(Value.mkInt32(8)))
  }

  ignore("Dimension.flix") {
    val t = new Tester().addPath("./examples/domains/Dimension.flix")
    t.checkSuccess()
  }

  test("StrictSign.flix") {
    val input =
      """namespace StrictSign {
        |    let Sign<> = (Sign.Bot, Sign.Top, leq, lub, glb);
        |    lat A(k: Int, v: Sign);
        |
        |    A(1, Sign.Neg).
        |    A(2, Sign.Zer).
        |    A(3, Sign.Pos).
        |
        |    A(4, Sign.Neg).
        |    A(4, Sign.Zer).
        |    A(4, Sign.Pos).
        |
        |    A(5, x) :- A(1, x), A(2, x), A(3, x).
        |
        |    A(6, plus(Sign.Zer, Sign.Pos)).
        |    A(7, plus(Sign.Neg, Sign.Pos)).
        |
        |    A(8, times(Sign.Zer, Sign.Pos)).
        |    A(9, times(Sign.Neg, Sign.Neg)).
        |}
      """.stripMargin

    val t = new Tester()
      .addPath("./examples/domains/Belnap.flix")
      .addPath("./examples/domains/StrictSign.flix")
      .addStr(input)
      .run()

    val Sign = Symbol.Resolved.mk(List("StrictSign", "Sign"))

    val Neg = Value.mkTag(Sign, "Neg", Value.Unit)
    val Zer = Value.mkTag(Sign, "Zer", Value.Unit)
    val Pos = Value.mkTag(Sign, "Pos", Value.Unit)
    val Top = Value.mkTag(Sign, "Top", Value.Unit)

    t.checkValue(List(Neg), "StrictSign/A", List(Value.mkInt32(1)))
    t.checkValue(List(Zer), "StrictSign/A", List(Value.mkInt32(2)))
    t.checkValue(List(Pos), "StrictSign/A", List(Value.mkInt32(3)))
    t.checkValue(List(Top), "StrictSign/A", List(Value.mkInt32(4)))
    t.checkNone("StrictSign/A", List(Value.mkInt32(5)))
    t.checkValue(List(Pos), "StrictSign/A", List(Value.mkInt32(6)))
    t.checkValue(List(Top), "StrictSign/A", List(Value.mkInt32(7)))
    t.checkValue(List(Zer), "StrictSign/A", List(Value.mkInt32(8)))
    t.checkValue(List(Pos), "StrictSign/A", List(Value.mkInt32(9)))
  }

  test("Type.flix") {
    val t = new Tester().addPath("./examples/domains/Type.flix")
    t.checkSuccess()
  }


  /////////////////////////////////////////////////////////////////////////////
  // Entities                                                                //
  /////////////////////////////////////////////////////////////////////////////

  test("Bank.flix") {
    val t = new Tester().addPath("./examples/entities/Bank.flix")
    t.checkSuccess()
  }

  test("Cinema.flix") {
    val t = new Tester().addPath("./examples/entities/Cinema.flix")
    t.checkSuccess()
  }

  test("Company.flix") {
    val t = new Tester().addPath("./examples/entities/Company.flix")
    t.checkSuccess()
  }

  test("Hotel.flix") {
    val t = new Tester().addPath("./examples/entities/Hotel.flix")
    t.checkSuccess()
  }

  test("Library.flix") {
    val t = new Tester().addPath("./examples/entities/Library.flix")
    t.checkSuccess()
  }

  test("Manufacturer.flix") {
    val t = new Tester().addPath("./examples/entities/Manufacturer.flix")
    t.checkSuccess()
  }

  test("Realtor.flix") {
    val t = new Tester().addPath("./examples/entities/Realtor.flix")
    t.checkSuccess()
  }

  test("Tournament.flix") {
    val t = new Tester().addPath("./examples/entities/Tournament.flix")
    t.checkSuccess()
  }

}
