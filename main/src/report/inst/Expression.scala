package report.inst

sealed trait PType
sealed trait PBool extends PType
sealed trait PInt32 extends PType
sealed trait PInt64 extends PType
sealed trait PChar extends PType
sealed trait PReference[T <: PRefType] extends PType

sealed trait PRefType
sealed trait PString extends PRefType
sealed trait PUnit extends PRefType
sealed trait PArray[T <: PType] extends PRefType
sealed trait PAny extends PRefType

sealed trait Expression[T <: PType] { val tpe: RType[T] }

case class IntLit(i: Int) extends Expression[PInt32] {
  val tpe: RType[PInt32] = RInt
}

case class CharLit(c: Char) extends Expression[PChar] {
  val tpe: RType[PChar] = RChar
}

case class Add(left: Expression[PInt32], right: Expression[PInt32]) extends Expression[PInt32] {
  val tpe: RType[PInt32] = RInt
}

//se class Eq(left: Expression[_ <: PType], right: Expression[_ <: PType])
case class Eq[T <: PType](left: Expression[T], right: Expression[T]) extends Expression[PInt32] {
  val tpe: RType[PInt32] = RInt
}

case class ArrayLookup[T <: PType](array: Expression[PReference[PArray[T]]], index: Expression[PInt32])
  extends Expression[T] {
  def arrayInnerMatch[TT <: PType](inner: RRefType[PArray[TT]]): RType[TT] = inner match {
    case RArray(inner) =>
      inner
  }

  val tpe: RType[T] = array.tpe match {
    //case RInt => ???
    case RReference(reference) => arrayInnerMatch(reference)
  }
}

sealed trait RType[T <: PType]
object RBool extends RType[PInt32]
object RInt extends RType[PInt32]
object RChar extends RType[PChar]
case class RReference[T <: PRefType](reference: RRefType[T]) extends RType[PReference[T]]
sealed trait RRefType[T <: PRefType]
object RString extends RRefType[PString]
object RUnit extends RRefType[PUnit]
case class RArray[T <: PType](inner: RType[T]) extends RRefType[PArray[T]]
case class RTuple(inner: List[RType[_ <: PType]]) extends RRefType[PAny]


object Compiler {

  import Ins._

  sealed trait Stack

  sealed trait StackNil extends Stack

  sealed trait StackCons[R <: Stack, T <: PType] extends Stack

  type **[R <: Stack, T <: PType] = StackCons[R, T]

  sealed class F[R <: Stack] {
    def emitCode(instruction: String, rest: Any*): Unit = ()
  }

  def compile[R <: Stack, T <: PType](exp: Expression[T]): F[R] => F[R ** T] = {
    exp match {
      case IntLit(i) => pushInt(i)
      case CharLit(c) => pushChar[R](c)
      case Add(left, right) =>
        ANN[R] ~
          compile(left) ~
          compile(right) ~
          ADD
      case Eq(left, right) =>
        //compile[R, ???](left) ~
        ANN[R] ~
          compile(left) ~
          compile(right) ~
          XEQ(left.tpe)
      //try INTEQ
      //inline doesn't work
      case a@ArrayLookup(array, index) =>
        ANN[R] ~
          compile(array) ~
          compile(index) ~
          XALOAD(a.tpe)
    }
  }
}


object Ins {

  import Compiler._

  def pushInt[R <: Stack](i: Int): F[R] => F[R ** PInt32] = ???

  def pushChar[R <: Stack](c: Char): F[R] => F[R ** PChar] = ???

  def ADD[R <: Stack]: F[R ** PInt32 ** PInt32] => F[R ** PInt32] = f => {
    f.emitCode("ADD")
    f.asInstanceOf[F[R ** PInt32]]
  }

  def INTEQ[R <: Stack]: F[R ** PInt32 ** PInt32] => F[R ** PInt32] = ???

  def CHAREQ[R <: Stack]: F[R ** PChar ** PChar] => F[R ** PInt32] = ???

  def OBJEQ[R <: Stack, T <: PRefType]: F[R ** PReference[T] ** PReference[T]] => F[R ** PInt32] = ???

  def XEQ[R <: Stack, T <: PType](e: RType[T]): F[R ** T ** T] => F[R ** PInt32] = e match {
    case RBool | RInt => INTEQ
    case RChar => CHAREQ
    case RReference(_) => OBJEQ
  }

  def XALOAD[R <: Stack, T <: PType](e: RType[T]): F[R ** PReference[PArray[T]] ** PInt32] => F[R ** T] = ???

  def TUPLELOAD[R <: Stack, T <: PType](e: RType[T]): F[R ** PReference[PAny] ** PInt32] => F[R ** T] = ???

  def ANN[R <: Stack]: F[R] => F[R] = f => f

  implicit class Compose[A <: Stack, B <: Stack](ab: F[A] => F[B]) {
    def ~[C <: Stack](bc: F[B] => F[C]): F[A] => F[C] =
      f => bc(ab(f))
  }

}