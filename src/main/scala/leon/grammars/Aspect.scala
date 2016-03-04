/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package grammars

import purescala.Expressions.Expr
import utils.SeqUtils._
import Tags._

abstract class Aspect {
  def asString(implicit ctx: LeonContext): String

  def applyTo(p: ProductionRule[Label, Expr])(implicit ctx: LeonContext): Traversable[ProductionRule[Label, Expr]]
}

object Aspects {
  abstract class Peristant extends Aspect {
    def applyTo(p: ProductionRule[Label, Expr])(implicit ctx: LeonContext) = {
      List(p.copy(
        subTrees = p.subTrees.map(lab => lab.withAspect(this))
      ))
    }
  }

  case class Sized(size: Int) extends Aspect {
    def asString(implicit ctx: LeonContext) = "|"+size+"|"

    def applyTo(p: ProductionRule[Label, Expr])(implicit ctx: LeonContext) = {
      val optimizeCommut = true

      if (size <= 0) {
        Nil
      } else if (p.arity == 0) {
        if (size == p.cost) {
          List(p)
        } else {
          Nil
        }
      } else {
        val sizes = if(optimizeCommut && Tags.isCommut(p.tag) && p.subTrees.toSet.size == 1) {
          sumToOrdered(size - p.cost, p.arity)
        } else {
          sumTo(size - p.cost, p.arity)
        }

        for (ss <- sizes) yield {
          val newSubTrees = (p.subTrees zip ss).map {
            case (lab, s) => lab.withAspect(Sized(s))
          }

          ProductionRule(newSubTrees, p.builder, p.tag)
        }
      }
    }
  }

  case class Tagged(tag: Tag, pos: Int, isConst: Option[Boolean]) extends Aspect {
    private val cString = isConst match {
      case Some(true) => "↓"
      case Some(false) => "↑"
      case None => "○"
    }

    /** [[isConst]] is printed as follows: ↓ for constants only, ↑ for nonconstants only,
      * ○ for anything allowed.
      */
    override def asString(implicit ctx: LeonContext): String = s"$tag@$pos$cString"


    def applyTo(p: ProductionRule[Label, Expr])(implicit ctx: LeonContext) = {

      // If const-ness is explicit, make sure the production has similar const-ness
      val constValid = isConst match {
        case Some(b) => Tags.isConst(p.tag) == b
        case None    => true
      }

      // Tags to avoid depending on parent aspect
      val excludedTags: Set[Tag] = (tag, pos) match {
        case (Top,   _)             => Set()
        case (And,   0)             => Set(And, BooleanC)
        case (And,   1)             => Set(BooleanC)
        case (Or,    0)             => Set(Or, BooleanC)
        case (Or,    1)             => Set(BooleanC)
        case (Plus,  0)             => Set(Plus, Zero, One)
        case (Plus,  1)             => Set(Zero)
        case (Minus, 1)             => Set(Zero)
        case (Not,   _)             => Set(Not, BooleanC)
        case (Times, 0)             => Set(Times, Zero, One)
        case (Times, 1)             => Set(Zero, One)
        case (Equals,_)             => Set(Not, BooleanC)
        case (Div | Mod, 0 | 1)     => Set(Zero, One)
        case (FunCall(true, _), 0)  => Set(Constructor(true)) // Don't allow Nil().size etc.
        case _                      => Set()
      }

      val tagsValid = !(excludedTags contains p.tag)

      def powerSet[A](t: Set[A]): Set[Set[A]] = {
        @scala.annotation.tailrec
        def pwr(t: Set[A], ps: Set[Set[A]]): Set[Set[A]] =
          if (t.isEmpty) ps
          else pwr(t.tail, ps ++ (ps map (_ + t.head)))

        pwr(t, Set(Set.empty[A]))
      }

      if (constValid && tagsValid) {
        val subAspects = if (p.isTerminal || Tags.allConstArgsAllowed(p.tag)) {
          Seq(p.subTrees.indices.map { i =>
            Tagged(p.tag, i, None)
          })
        } else {
          // All positions are either forced to be const or forced to be
          // non-const. We don't want all consts though.
          val indices = p.subTrees.indices.toSet

          (powerSet(indices) - indices) map { isConst =>
            p.subTrees.indices.map { i =>
              Tagged(p.tag, i, Some(isConst(i)))
            }
          }
        }

        for (as <- subAspects) yield {
          val newSubTrees = (p.subTrees zip as).map { case (lab, a) =>
            lab.withAspect(a)
          }

          ProductionRule(newSubTrees, p.builder, p.tag, p.cost)
        }
      } else {
        Nil
      }
    }
  }
}
