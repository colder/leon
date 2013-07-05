import leon.Utils._

object List1 {
  abstract class List
  case class Cons(h: Int, t: List) extends List
  case object Nil extends List

  def size(l: List): Int = l match {
    case Cons(h, t) => 1 + size(t)
    case Nil => 0
  }

  def test2(i: Int): List = Cons(i, Nil)

  def test(i: Int): List = {
    choose{ (x: List) => size(x) == i }
  }

  def main(args: Array[String]) {
    test(10)
  }
}
