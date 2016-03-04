/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package grammars

import purescala.Expressions.Expr
import utils.SeqUtils._

abstract class Aspect {
  def asString(implicit ctx: LeonContext): String

  def applyTo(p: ProductionRule[Label, Expr])(implicit ctx: LeonContext): Seq[ProductionRule[Label, Expr]]
}

object Aspects {
  abstract class Peristant extends Aspect {
    def applyTo(p: ProductionRule[Label, Expr])(implicit ctx: LeonContext): Seq[ProductionRule[Label, Expr]] = {
      List(p.copy(
        subTrees = p.subTrees.map(lab => lab.withAspect(this))
      ))
    }


  }

  case class Sized(size: Int) extends Aspect {
    def asString(implicit ctx: LeonContext) = "|"+size+"|"

    def applyTo(p: ProductionRule[Label, Expr])(implicit ctx: LeonContext): Seq[ProductionRule[Label, Expr]] = {
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
        println("Decomposing "+(size-p.cost)+" in "+p.arity + "; sizes: "+sizes)

        for (ss <- sizes) yield {
          val newSubTrees = (p.subTrees zip ss).map {
            case (lab, s) => lab.withAspect(Sized(s))
          }

          ProductionRule(newSubTrees, p.builder, p.tag)
        }
      }
    }
  }
}
