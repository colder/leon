import leon._
import leon.lang._
import leon.lang.synthesis._
import leon.collection._
import leon.annotation._


object Parser {

  abstract class Token
  case object TPlus extends Token
  case object TMinus extends Token
  case class  TLit(v: BigInt) extends Token

  abstract class Tree
  case class Lit(v: BigInt) extends Tree
  case class Plus(a: Tree, b: Tree) extends Tree
  case class Minus(a: Tree, b: Tree) extends Tree

  abstract class ParseResult {
    def isValid: Boolean
    def isEnd: Boolean

    def compose(f: Tree => Tree) = {
      this match {
        case ParseOk(t, res) => ParseOk(f(t), res)
        case _ => ParseError
      }
    }
  }

  case class ParseOk(t: Tree, rest: List[Token]) extends ParseResult {
    override def isValid = true
    override def isEnd = rest.isEmpty

  }

  case object ParseError extends ParseResult {
    override def isValid = false
    override def isEnd   = true
  }


  def parse(in: List[Token]): ParseResult = {
    ???[ParseResult]
    //in match {
    //  case Cons(TLit(v), Cons(TPlus, r)) => parse(r)
    //  case Cons(TLit(v), Cons(TMinus, r)) => parse(r)
    //  case Cons(TLit(v), Nil()) => ParseOk(Nil())
    //  case Nil() => ParseOk(Nil())
    //  case _ => ParseError
    //}
  } ensuring { out =>
    out.isEnd &&
    parsingTests(in, out)
  }



  @inline
  def parsingTests(in: List[Token], out: ParseResult): Boolean = {
    (in, out) passes {
      // Good examples
      case Cons(TLit(a), Cons(TPlus, Cons(TLit(b), Nil())))                              => ParseOk(Plus(Lit(a), Lit(b)), Nil())
      case Cons(TLit(a), Cons(TMinus, Cons(TLit(b), Nil())))                             => ParseOk(Minus(Lit(a), Lit(b)), Nil())
      case Cons(TLit(a), Cons(TMinus, Cons(TLit(b), Cons(TPlus, Cons(TLit(c), Nil()))))) => ParseOk(Plus(Minus(Lit(a), Lit(b)), Lit(c)), Nil())
      case Cons(TLit(a), Nil())                                                          => ParseOk(Lit(a), Nil())

      // Bad examples
      case Cons(TPlus, Nil())                                               => ParseError
      case Cons(TMinus, Cons(TLit(_), Cons(TLit(_), Nil())))                => ParseError
      case Cons(TLit(_), Cons(TMinus, Cons(TLit(_), Cons(TLit(_), Nil())))) => ParseError
      case Cons(TLit(_), Cons(TLit(_), Cons(TLit(_), Nil())))               => ParseError
      case Cons(TLit(_), Cons(TLit(_), Nil()))                              => ParseError
      case Cons(TPlus, Cons(TPlus, Nil()))                                  => ParseError
      case Cons(TPlus, Cons(TMinus, Nil()))                                 => ParseError
      case Cons(TMinus, Cons(TPlus, Nil()))                                 => ParseError
      case Cons(TMinus, Cons(TMinus, Nil()))                                => ParseError
      case Nil()                                                            => ParseError
    }
  }


}
