/*
 * Copyright 2024 Jonathan Lindegaard Starup
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
package ca.uwaterloo.flix.language.phase.unification

import ca.uwaterloo.flix.language.ast.SourceLocation
import ca.uwaterloo.flix.language.phase.unification.BooleanFuzzer.RawString.toRawString
import ca.uwaterloo.flix.language.phase.unification.FastSetUnification.{Equation, Term}
import ca.uwaterloo.flix.util.{InternalCompilerException, Result}

import scala.annotation.tailrec
import scala.collection.immutable.SortedSet
import scala.collection.mutable
import scala.collection.mutable.ListBuffer
import scala.util.Random

object BooleanFuzzer {

  private implicit val loc: SourceLocation = SourceLocation.Unknown

  /**
    * Contains the constructors of a boolean algebra [[T]].
    */
  case class FormulaFormer[T](
                               top: T,
                               bot: T,
                               cst: Int => T,
                               varr: Int => T,
                               elem: Int => T,
                               union: List[T] => T,
                               inter: List[T] => T,
                               compl: T => T
                             )

  /**
    * The former of [[Term]].
    */
  def termFormer(): FormulaFormer[Term] = FormulaFormer(
    Term.Univ,
    Term.Empty,
    Term.Cst,
    Term.Var,
    Term.mkElemSet(_: Int),
    Term.mkUnion(_: List[Term]),
    Term.mkInter(_: List[Term]),
    Term.mkCompl
  )

  /**
    * Constructs a random boolean algebra formula.
    *
    * @param former constructors for the boolean algebra
    * @param r object for random choice
    * @param depth the maximum depth of the formula
    * @param csts the size of the universe of constants, e.g. 0 means no constants
    * @param vars the size of the universe of variables, e.g. 0 means no variables
    * @param elems the size of the universe of elements, e.g. 0 means no elements
    * @tparam T the type of the underlying formula
    * @return the random formula
    */
  def randomTerm[T](former: FormulaFormer[T], r: Random, depth: Int, csts: Int, vars: Int, elems: Int): T = {
    if (csts <= 0 && vars <= 0 && elems <= 0 && depth <= 0) former.bot
    else r.nextInt(6) match {
      case 0 if csts <= 0 => randomTerm(former, r, depth, csts, vars, elems)
      case 0 => former.cst(r.nextInt(csts))
      case 1 if vars <= 0 => randomTerm(former, r, depth, csts, vars, elems)
      case 1 => former.varr(csts + r.nextInt(vars))
      case 2 if elems <= 0 => randomTerm(former, r, depth, csts, vars, elems)
      case 2 => former.elem(csts + vars + r.nextInt(elems))
      case 3 if depth <= 0 => randomTerm(former, r, depth, csts, vars, elems)
      case 3 => former.compl(randomTerm(former, r, depth - 1, csts, vars, elems))
      case 4 if depth <= 0 => randomTerm(former, r, depth, csts, vars, elems)
      case 4 => former.inter(List.fill(r.nextInt(4) + 1)(randomTerm(former, r, depth - 1, csts, vars, elems)))
      case 5 if depth <= 0 => randomTerm(former, r, depth, csts, vars, elems)
      case 5 => former.union(List.fill(r.nextInt(4) + 1)(randomTerm(former, r, depth - 1, csts, vars, elems)))
    }
  }

  def main(args: Array[String]): Unit = {
    fuzz(new Random(), 2000_000, 5, -1)
  }

  def fuzz(random: Random, testLimit: Int, errLimit: Int, timeoutLimit: Int): Boolean = {
    val former = termFormer()
    val errs: ListBuffer[Term] = ListBuffer.empty
    val errPhaseFrequence = mutable.Map.empty[Int, Int]
    val timeouts: ListBuffer[Term] = ListBuffer.empty
    val timeoutPhaseFrequence = mutable.Map.empty[Int, Int]
    var continue = true
    var tests = 0
    while (continue && tests < testLimit) {
      if (tests % 10_000 == 0) {
        val errAmount = errs.length
        val timeoutAmount = timeouts.length
        println(s"${tests/1000}k (${(tests-errAmount-timeoutAmount)/1000}k, ${errAmount} errs, ${timeoutAmount} t.o.)")
      }
      tests += 1
      val t = randomTerm(former, random, 8, 6, 6, 6)
      val (res, phase) = eqSelf(t, Some(random))
      res match {
        case Res.Pass => ()
        case Res.Fail =>
          errs += Term.mkXor(t, t)
          inc(errPhaseFrequence, phase)
          if (errLimit > 0 && errs.sizeIs >= errLimit) continue = false
        case Res.Timeout =>
          timeouts += Term.mkXor(t, t)
          inc(timeoutPhaseFrequence, phase)
          if (timeoutLimit > 0 && timeouts.sizeIs >= timeoutLimit) continue = false
      }
    }
    println()
    println(s"   Tests: $tests")
    val errSize = errs.size
    println(s"    Errs: $errSize (${errSize/(1.0*tests) * 100} %)")
    val timeoutSize = timeouts.size
    println(s"Timeouts: $timeoutSize (${timeoutSize/(1.0*tests) * 100} %)")
    if (errPhaseFrequence.nonEmpty) println(s"Err phases:")
    errPhaseFrequence.toList.sorted.foreach(p => println(s"\t\tphase ${p._1}: ${p._2} errors"))
    if (timeoutPhaseFrequence.nonEmpty) println(s"Timeout phases:")
    timeoutPhaseFrequence.toList.sorted.foreach(p => println(s"\t\tphase ${p._1}: ${p._2} timeouts"))
    if (errs.nonEmpty) println(s"Smallest error:")
    errs.sortBy(_.size).headOption.foreach(err => println(s"> ${err.toString}\n> ${toRawString(err)}"))
    if (timeouts.nonEmpty) println(s"Smallest timeout:")
    timeouts.sortBy(_.size).headOption.foreach(timeout => println(s"> ${timeout.toString}\n> ${toRawString(timeout)}"))
    errs.isEmpty
  }

  private def inc[K](m: mutable.Map[K, Int], k: K): Unit = {
    m.updateWith(k)(opt => Some(opt.getOrElse(0) + 1))
  }

  private sealed trait Res {
    def passed: Boolean = this match {
      case Res.Pass => true
      case Res.Fail => false
      case Res.Timeout => false
    }
  }
  private object Res {
    case object Pass extends Res
    case object Fail extends Res
    case object Timeout extends Res
  }

  private def eqSelf(t: Term, explode: Option[Random]): (Res, Int) = {
    val eq = Term.mkXor(t, t) ~ Term.Empty
    val eqs = explode match {
      case Some(r) => explodeKnownEquation(r, eq)
      case None => List(eq)
    }
    val (res, phase) = FastSetUnification.solveAllInfo(eqs)
    res match {
      case Result.Ok(subst) => try {
        FastSetUnification.verify(subst, eqs)
        (Res.Pass, phase)
      } catch {
        case ex: InternalCompilerException => (Res.Fail, phase)
      }
      case Result.Err((ex, _, _)) if ex.isInstanceOf[FastSetUnification.TooComplexException] =>
        (Res.Timeout, phase)
      case Result.Err((_, _, _)) =>
        (Res.Fail, phase)
    }
  }

  /**
    * Takes an equation and creates equations that names some subterms as variables via extra equations.
    */
  private def explodeKnownEquation(r: Random, eq: Equation): List[Equation] = {
    var next = maxId(eq.t1) max maxId(eq.t2)
    def getId(): Int = {
      next += 1
      next
    }
    val (left, leftEqs) = explode(r, eq.t1, eq.loc, getId())
    val (right, rightEqs) = explode(r, eq.t2, eq.loc, getId())
    Equation.mk(left, right, eq.loc) :: leftEqs ++ rightEqs
  }

  private def explode(r: Random, t: Term, loc: SourceLocation, gen: => Int): (Term, List[Equation]) = t match {
    case Term.Univ | Term.Empty | Term.Cst(_) | Term.ElemSet(_) | Term.Var(_) =>
      if (r.nextInt(5) == 0) {
        val fresh = Term.Var(gen)
        (fresh, List(Equation.mk(fresh, t, loc)))
      } else (t, Nil)
    case Term.Compl(t0) =>
      val (t, eqs) = explode(r, t0, loc, gen)
      if (r.nextInt(3) == 0) {
        val fresh = Term.Var(gen)
        (fresh, Equation.mk(fresh, Term.Compl(t), loc) :: eqs)
      } else (t, eqs)
    case Term.Inter(posElem, posCsts, posVars, negElem, negCsts, negVars, rest) =>
      splitTerms(Term.mkInter, r, loc, gen, posElem, posCsts, posVars, negElem, negCsts, negVars, rest)
    case Term.Union(posElem, posCsts, posVars, negElem, negCsts, negVars, rest) =>
      splitTerms(Term.mkUnion, r, loc, gen, posElem, posCsts, posVars, negElem, negCsts, negVars, rest)
  }

  private def splitTerms(build: List[Term] => Term, r: Random, loc: SourceLocation, gen: => Int, posElem: Option[Term.ElemSet], posCsts: Set[Term.Cst], posVars: Set[Term.Var], negElem: Option[Term.ElemSet], negCsts: Set[Term.Cst], negVars: Set[Term.Var], rest0: List[Term]): (Term, List[Equation]) = {
    var eqs: List[Equation] = Nil
    var rest: List[Term] = Nil
    for (r0 <- rest0) {
      val (rr, eq) = explode(r, r0, loc, gen)
      rest = rr :: rest
      eqs = eq ++ eqs
    }
    val terms0: List[Term] = posElem.toList ++ posCsts.toList ++ posVars.toList ++ negElem.toList.map(Term.mkCompl) ++ negCsts.toList.map(Term.mkCompl) ++ negVars.toList.map(Term.mkCompl) ++ rest
    val terms = r.shuffle(terms0)
    // chose between at least 1 and at most terms - 2 or 4
    val maxRoll = 4 min ((terms.size - 2) max 0)
    val chunkAmount = if (maxRoll <= 0) 1 else r.nextInt(maxRoll) + 1
    // reserve chunkAmount elements to have them non-empty
    var (reserved, remaining) = terms.splitAt(chunkAmount)
    var chunks: List[List[Term]] = Nil
    for (i <- Range(0, chunkAmount)) {
      val (hd, reserved1) = (reserved.head, reserved.drop(1))
      reserved = reserved1
      if (remaining.isEmpty) {
        chunks = List(hd) :: chunks
      } else {
        val index = if (i == chunkAmount - 1) remaining.size else r.nextInt(remaining.size+1)
        val (mine, remaining1) = remaining.splitAt(index)
        remaining = remaining1
        chunks = (hd :: mine) :: chunks
      }
    }
    assert(reserved.isEmpty)
    assert(remaining.isEmpty, remaining.size)
    var finalTerms: List[Term] = Nil
    for (chunk <- chunks) {
      if (r.nextInt(4) != 0) {
        val fresh = Term.Var(gen)
        eqs = Equation.mk(fresh, build(chunk), loc) :: eqs
        finalTerms = fresh :: finalTerms
      } else {
        finalTerms = chunk ++ finalTerms
      }
    }
    (build(finalTerms), eqs)
  }

  @tailrec
  private def maxId(t: Term): Int = t match {
    case Term.Univ => -1
    case Term.Empty => -1
    case Term.Cst(c) => c
    case Term.Var(x) => x
    case Term.ElemSet(s) => maxId(s)
    case Term.Compl(t) => maxId(t)
    case Term.Inter(posElem, posCsts, posVars, negElem, negCsts, negVars, rest) =>
      maxId(posElem) max maxId(posCsts) max maxId(posVars) max maxId(negElem) max maxId(negCsts) max maxId(negVars) max maxId(rest)
    case Term.Union(posElem, posCsts, posVars, negElem, negCsts, negVars, rest) =>
      maxId(posElem) max maxId(posCsts) max maxId(posVars) max maxId(negElem) max maxId(negCsts) max maxId(negVars) max maxId(rest)
  }

  private def maxId(l: List[Term]): Int = {
    if (l.isEmpty) -1 else l.map(maxId).max
  }

  private def maxId(s: Set[_ <: Term]): Int = {
    if (s.isEmpty) -1 else s.map(maxId).max
  }

  private def maxId(s: SortedSet[Int]): Int = {
    if (s.isEmpty) -1 else s.max
  }

  private def maxId(o: Option[Term.ElemSet]): Int = {
    o.map(es => maxId(es.s)).getOrElse(-1)
  }

  object RawString {
    def toRawString(t: Term): String = t match {
      case Term.Univ => "Univ"
      case Term.Empty => "Empty"
      case Term.Cst(c) => s"Cst($c)"
      case Term.Var(x) => s"Var($x)"
      case Term.ElemSet(i) => s"ElemSet(SortedSet(${i.mkString(", ")}))"
      case Term.Compl(t) => s"Compl(${toRawString(t)})"
      case Term.Inter(posElem, posCsts, posVars, negElems, negCsts, negVars, rest) =>
        val pe = posElem match {
          case Some(value) => s"Some(${toRawString(value)})"
          case None => s"None"
        }
        s"Inter($pe, ${helpSet(posCsts)}, ${helpSet(posVars)}, ${helpSet(negElems)}, ${helpSet(negCsts)}, ${helpSet(negVars)}, ${helpList(rest)})"
      case Term.Union(posElems, posCsts, posVars, negElems, negCsts, negVars, rest) =>
        s"Union(${helpSet(posElems)}, ${helpSet(posCsts)}, ${helpSet(posVars)}, ${helpSet(negElems)}, ${helpSet(negCsts)}, ${helpSet(negVars)}, ${helpList(rest)})"
    }
    private def helpList(l: Iterable[Term]): String = l.map(toRawString).mkString("List(", ", ", ")")
    private def helpSet(l: Iterable[Term]): String = l.map(toRawString).mkString("Set(", ", ", ")")
  }

}
