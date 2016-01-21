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

  abstract class ParseResult {
    def isValid: Boolean
    def isEnd: Boolean
  }

  case class ParseOk(rest: List[Token]) extends ParseResult {
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
      case Cons(TLit(_), Cons(TPlus, Cons(TLit(_), Nil()))) => ParseOk(Nil())
      case Cons(TLit(_), Cons(TMinus, Cons(TLit(_), Nil()))) => ParseOk(Nil())
      case Cons(TLit(_), Nil()) => ParseOk(Nil())
      case Cons(TLit(_), Cons(TLit(_), _)) => ParseError
      case Cons(TLit(_), Nil()) => ParseOk(Nil())
      case Cons(TPlus, Cons(TMinus, _)) => ParseError
      case Cons(TMinus, Cons(TMinus, _)) => ParseError
      case Cons(TMinus, Cons(TPlus, _)) => ParseError
      case Cons(TLit(_), Cons(TMinus, Cons(TLit(_), Cons(TMinus, Cons(TLit(_), Nil()))))) => ParseOk(Nil())
    }
  }


}
