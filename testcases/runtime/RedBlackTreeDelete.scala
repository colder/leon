import scala.collection.immutable.Set
import leon.Annotations._
import leon.Utils._

object RedBlackTreeDelete {
  sealed abstract class Color
  case class Red() extends Color
  case class Black() extends Color

  sealed abstract class Tree
  case class Empty() extends Tree
  case class Node(color: Color, left: Tree, value: Int, right: Tree) extends Tree

  sealed abstract class OptionInt
  case class Some(v : Int) extends OptionInt
  case class None() extends OptionInt

  def content(t: Tree) : Set[Int] = t match {
    case Empty() => Set.empty
    case Node(_, l, v, r) => content(l) ++ Set(v) ++ content(r)
  }

  def size(t: Tree) : Int = (t match {
    case Empty() => 0
    case Node(_, l, v, r) => size(l) + 1 + size(r)
  }) ensuring(_ >= 0)

  /* We consider leaves to be black by definition */
  def isBlack(t: Tree) : Boolean = t match {
    case Empty() => true
    case Node(Black(),_,_,_) => true
    case _ => false
  }

  def redNodesHaveBlackChildren(t: Tree) : Boolean = t match {
    case Empty() => true
    case Node(Black(), l, _, r) => redNodesHaveBlackChildren(l) && redNodesHaveBlackChildren(r)
    case Node(Red(), l, _, r) => isBlack(l) && isBlack(r) && redNodesHaveBlackChildren(l) && redNodesHaveBlackChildren(r)
  }

  def redDescHaveBlackChildren(t: Tree) : Boolean = t match {
    case Empty() => true
    case Node(_,l,_,r) => redNodesHaveBlackChildren(l) && redNodesHaveBlackChildren(r)
  }

  def blackBalanced(t : Tree) : Boolean = t match {
    case Node(_,l,_,r) => blackBalanced(l) && blackBalanced(r) && blackHeight(l) == blackHeight(r)
    case Empty() => true
  }

  def blackHeight(t : Tree) : Int = t match {
    case Empty() => 1
    case Node(Black(), l, _, _) => blackHeight(l) + 1
    case Node(Red(), l, _, _) => blackHeight(l)
  }

  // <<insert element x into the tree t>>
  def ins(x: Int, t: Tree): Tree = {
    require(redNodesHaveBlackChildren(t) && blackBalanced(t))
    t match {
      case Empty() => Node(Red(),Empty(),x,Empty())
      case Node(c,a,y,b) =>
        if      (x < y)  balance(c, ins(x, a), y, b)
        else if (x == y) Node(c,a,y,b)
        else             balance(c,a,y,ins(x, b))
    }
  } ensuring (res => content(res) == content(t) ++ Set(x) 
                   && size(t) <= size(res) && size(res) <= size(t) + 1
                   && redDescHaveBlackChildren(res)
                   && blackBalanced(res))

  def insSynth(x: Int, t: Tree): Tree = {
    choose { (res: Tree) => content(res) == content(t) ++ Set(x) &&
                   size(t) <= size(res) && size(res) <= size(t) + 1 &&
                   redDescHaveBlackChildren(res) &&
                   blackBalanced(res) &&
                   redNodesHaveBlackChildren(t) && blackBalanced(t) }
  }


  def makeBlack(n: Tree): Tree = {
    require(redDescHaveBlackChildren(n) && blackBalanced(n))
    n match {
      case Node(Red(),l,v,r) => Node(Black(),l,v,r)
      case _ => n
    }
  } ensuring(res => redNodesHaveBlackChildren(res) && blackBalanced(res))

  def add(x: Int, t: Tree): Tree = {
    require(redNodesHaveBlackChildren(t) && blackBalanced(t))
    makeBlack(ins(x, t))
  } ensuring (res => content(res) == content(t) ++ Set(x) && redNodesHaveBlackChildren(res) && blackBalanced(res))

  def addSynth(x: Int, t: Tree): Tree = {
    require(redNodesHaveBlackChildren(t) && blackBalanced(t))

    choose {
      (res: Tree) => content(res) == content(t) ++ Set(x) && redNodesHaveBlackChildren(res) && blackBalanced(res)
    }
  }

  def deleteSynth(x: Int, t: Tree): Tree = {
    require(redNodesHaveBlackChildren(t) && blackBalanced(t))

    choose {
      (res: Tree) => content(res) == content(t) -- Set(x) && redNodesHaveBlackChildren(res) && blackBalanced(res)
    }
  }

  def balance(c: Color, a: Tree, x: Int, b: Tree): Tree = {
    Node(c,a,x,b) match {
      case Node(Black(),Node(Red(),Node(Red(),a,xV,b),yV,c),zV,d) => 
        Node(Red(),Node(Black(),a,xV,b),yV,Node(Black(),c,zV,d))
      case Node(Black(),Node(Red(),a,xV,Node(Red(),b,yV,c)),zV,d) => 
        Node(Red(),Node(Black(),a,xV,b),yV,Node(Black(),c,zV,d))
      case Node(Black(),a,xV,Node(Red(),Node(Red(),b,yV,c),zV,d)) => 
        Node(Red(),Node(Black(),a,xV,b),yV,Node(Black(),c,zV,d))
      case Node(Black(),a,xV,Node(Red(),b,yV,Node(Red(),c,zV,d))) => 
        Node(Red(),Node(Black(),a,xV,b),yV,Node(Black(),c,zV,d))
      case Node(c,a,xV,b) => Node(c,a,xV,b)
    }
  } ensuring (res => content(res) == content(Node(c,a,x,b)))// && redDescHaveBlackChildren(res))

  def main(args: Array[String]) {
    val e = 1

    val tree0  = (Empty(): Tree)
    val tree1  = add(1, tree0)
    val tree2  = add(2, tree1)
    val tree3  = add(3, tree2)
    val tree4  = add(4, tree3)
    val tree5  = add(5, tree4)
    val tree6  = add(6, tree5)
    val tree7  = add(7, tree6)
    val tree8  = add(8, tree7)
    val tree9  = add(9, tree8)
    val tree10 = add(10, tree9)

    deleteSynth(e, tree0)
    deleteSynth(e, tree1)
    deleteSynth(e, tree2)
    deleteSynth(e, tree3)
    deleteSynth(e, tree4)
    deleteSynth(e, tree5)
    deleteSynth(e, tree6)
    deleteSynth(e, tree7)
    deleteSynth(e, tree8)
    deleteSynth(e, tree9)
    deleteSynth(e, tree10)
  }
}
