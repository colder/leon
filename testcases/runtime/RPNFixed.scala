import leon.lang._
import leon.annotation._
import leon.lang.synthesis._
import leon.collection._
import scala.reflect.runtime.universe._
import scala.reflect.api.{TypeCreator, Universe, Mirror}


import scala.collection.immutable.{List => ScalaList, Nil => ScalaNil}

object RPNFixed {
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
    }

    print(" Stack: [ ")
    d(s.stack)
    println(" ], Quit = "+s.quit)
  }

  def replStep(state: State): State = {
    display(state)
    val a = getAction()
    interactive { implicit o: Oracle[State] =>
      performAction(state, a)
    }
  }

  def performAction(s: State, a: Action) = withOracle { implicit o: Oracle[State] => {
    ???
  } ensuring { res =>
    if (s == State(Nil(), false) && a == IntV(2)) {
      res == State(Cons(2, Nil()), false)
    } else if (s == State(Cons(2, Nil()), false) && a == IntV(4)) {
      res == State(Cons(4, Cons(2, Nil())), false)
    } else if (s == State(Cons(4, Cons(2, Nil())), false) && a == IntV(8)) {
      res == State(Cons(8, Cons(4, Cons(2, Nil()))), false)
    } else if (s == State(Cons(8, Cons(4, Cons(2, Nil()))), false) && a == Plus) {
      res == State(Cons(12, Cons(2, Nil())), false)
    } else if (s == State(Cons(12, Cons(2, Nil())), false) && a == Plus) {
      res == State(Cons(14, Nil()), false)
    } else if (s == State(Cons(14, Nil()), false) && a == Quit) {
      res == State(Nil(), true)
    } else {
      true
    }
  }}

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
