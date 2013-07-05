import leon.Utils._

object Types {
  abstract class List
  case class Cons(h: Int, t: List) extends List
  case object Nil extends List

  def test(i: Int, l1: List, l2: List, s: Set[Int], b: Boolean): Int = {
    choose{ (x: Int) => x == i+2 }
  }

  def main(args: Array[String]) {
    test(42, Cons(41, Cons(42, Nil)), Nil, Set(1,2), true)
  }
}
