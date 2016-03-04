/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package grammars

import purescala.Expressions._
import purescala.Types._
import purescala.Common._
import transformers.Union
import utils.Timer

import scala.collection.mutable.{HashMap => MutableMap}

/** Represents a context-free grammar of expressions
  */
abstract class ExpressionGrammar {

  private[this] val cache = new MutableMap[Label, Seq[ProductionRule[Label, Expr]]]()

  /** The list of production rules for this grammar for a given nonterminal.
    * This is the cached version of [[getProductions]] which clients should use.
    *
    * @param lab The nonterminal for which production rules will be generated
    */
  def getProductions(lab: Label)(implicit ctx: LeonContext) = {
    cache.getOrElse(lab, {
      val res = computeProductions(lab)
      cache += lab -> res
      res
    })
  }

  /** The list of production rules for this grammar for a given nonterminal
    *
    * @param lab The nonterminal for which production rules will be generated
    */
  def computeProductions(lab: Label)(implicit ctx: LeonContext): Seq[ProductionRule[Label, Expr]]


  final def ||(that: ExpressionGrammar): ExpressionGrammar = {
    Union(Seq(this, that))
  }

  final def printProductions(printer: String => Unit)(implicit ctx: LeonContext) {
    for ((lab, gs) <- cache) {
      val lhs = f"${Console.BOLD}${lab.asString}%50s${Console.RESET} ::="
      if (gs.isEmpty) {
        printer(s"$lhs ε")
      } else for (g <- gs) {
        val subs = g.subTrees.map { t =>
          FreshIdentifier(Console.BOLD + t.asString + Console.RESET, t.getType).toVariable
        }

        val gen = g.builder(subs).asString

        printer(s"$lhs $gen")
      }
    }
  }
}

abstract class SimpleExpressionGrammar extends ExpressionGrammar {

  type Prod = ProductionRule[TypeTree, Expr]

  /** Generates a [[ProductionRule]] without nonterminal symbols */
  def terminal(builder: => Expr, tag: Tags.Tag = Tags.Top, cost: Int = 1) = {
    ProductionRule[TypeTree, Expr](Nil, { (subs: Seq[Expr]) => builder }, tag, cost)
  }

  /** Generates a [[ProductionRule]] with nonterminal symbols */
  def nonTerminal(subs: Seq[TypeTree], builder: (Seq[Expr] => Expr), tag: Tags.Tag = Tags.Top, cost: Int = 1) = {
    ProductionRule[TypeTree, Expr](subs, builder, tag, cost)
  }

  def filter(f: Prod => Boolean) = {
    new SimpleExpressionGrammar {
      def computeProductions(lab: TypeTree)(implicit ctx: LeonContext) = {
        SimpleExpressionGrammar.this.computeProductions(lab).filter(f)
      }
    }
  }

  /** The list of production rules for this grammar for a given nonterminal
    *
    * @param lab The nonterminal for which production rules will be generated
    */
  def computeProductions(lab: Label)(implicit ctx: LeonContext): Seq[ProductionRule[Label, Expr]] = {

    def applyAspect(ps: Seq[ProductionRule[Label, Expr]], a: Aspect) = {
      ps.flatMap(a.applyTo(_))
    }

    var prods = computeProductions(lab.getType).map { p =>
      ProductionRule(p.subTrees.map(Label(_)), p.builder, p.tag, p.cost)
    }

    for (a <- lab.aspects) {
      prods = applyAspect(prods, a)
    }

    prods
  }

  def computeProductions(tpe: TypeTree)(implicit ctx: LeonContext): Seq[ProductionRule[TypeTree, Expr]]
}
