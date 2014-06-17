import leon.lang._
import leon.annotation._
import leon.lang.synthesis._
import leon.collection._
import scala.reflect.runtime.universe._
import scala.reflect.api.{TypeCreator, Universe, Mirror}


import scala.collection.immutable.{List => ScalaList, Nil => ScalaNil}

object RPN {
  case class State(stack: List[Int], quit: Boolean)

  sealed abstract class Action
  case object Plus extends Action
  case object Minus extends Action
  case object Times extends Action
  case object Quit extends Action
  case class IntV(i: Int) extends Action

  @extern
  def getAction(): Action = {
    try {
      print("rpn> ")
      readLine() match {
        case "q" => Quit
        case "+" => Plus
        case "-" => Minus
        case "*" => Times
        case i => IntV(i.toInt)
      }
    } catch {
      case _: Throwable =>
        Quit
    }
  }

  @extern
  def display(s: State) = {
    def d(stack: List[Int]): Unit = stack match {
      case Cons(h, t) =>
        print(h+" ")
        d(t)
      case Nil() =>
        println
    }

    print(" -> ")
    d(s.stack)
  }

  def replStep(state: State): State = {
    display(state)
    val a = getAction()
    interactive { implicit o: Oracle[State] =>
      performAction(state, a)
    }
  }

  def performAction(s: State, a: Action)(implicit o: Oracle[State]) = ???

  def runRepl(s: State): State = {
    if (s.quit) {
      s
    } else {
      val ns = replStep(s)
      runRepl(ns)
    }
  }

  def repl() = {
    runRepl(State(Nil(), false))
  }
}
