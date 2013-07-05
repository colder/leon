import leon.Utils._

object Basic {
  abstract class List
  case class Cons(h: Int, t: List) extends List
  case object Nil extends List

  def test(a: Int): Int = {
    choose{ (x: Int) => x == a+2 }
  }

  def main(args: Array[String]) {
    test(42)
  }
}
