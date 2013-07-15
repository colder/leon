import leon.Utils._

object SortedList {
  abstract class List
  case class Cons(h: Int, t: List) extends List
  case object Nil extends List

  def size(l: List): Int = l match {
    case Cons(h, t) => 1 + size(t)
    case Nil => 0
  }

  def content(l: List): Set[Int] = l match {
    case Cons(h, t) => Set(h) ++ content(t)
    case Nil => Set()
  }

  case class CachedList(last: Int, data: List)

  def inv(cl: CachedList) = content(cl.data) contains cl.last || cl.data == Nil

  def cached(l: List): CachedList = choose {
    (x: CachedList) => isCachedList(x) && content(x.data) == content(l)
  }

  def insertSynth(l: CachedList, i: Int): List = {
    require(inv(l))
    choose{ (x: CachedList) => content(x.data) == content(l.data) ++ Set(i) && inv(x) }
  }

  def main(args: Array[String]) {
    val e = 42;

    insertSynth(Nil, e)
    insertSynth(Cons(1, Nil), e)
    insertSynth(Cons(1, Cons(2, Nil)), e)
    insertSynth(Cons(1, Cons(2, Cons(3, Nil))), e)
    insertSynth(Cons(1, Cons(2, Cons(3, Cons(4, Nil)))), e)
    insertSynth(Cons(1, Cons(2, Cons(3, Cons(4, Cons(5, Nil))))), e)
    insertSynth(Cons(1, Cons(2, Cons(3, Cons(4, Cons(5, Cons(6, Nil)))))), e)
    insertSynth(Cons(1, Cons(2, Cons(3, Cons(4, Cons(5, Cons(6, Cons(7, Nil))))))), e)
    insertSynth(Cons(1, Cons(2, Cons(3, Cons(4, Cons(5, Cons(6, Cons(7, Cons(8, Nil)))))))), e)
    insertSynth(Cons(1, Cons(2, Cons(3, Cons(4, Cons(5, Cons(6, Cons(7, Cons(8, Cons(9, Nil))))))))), e)
    insertSynth(Cons(1, Cons(2, Cons(3, Cons(4, Cons(5, Cons(6, Cons(7, Cons(8, Cons(9, Cons(10, Nil)))))))))), e)

    ()
  }
}
