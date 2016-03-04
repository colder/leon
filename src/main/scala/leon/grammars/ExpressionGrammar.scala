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

  type Prod = ProductionRule[Label, Expr]

  private[this] val cache = new MutableMap[Label, Seq[Prod]]()

  /** Generates a [[ProductionRule]] without nonterminal symbols */
  def terminal(builder: => Expr, tag: Tags.Tag = Tags.Top, cost: Int = 1) = {
    ProductionRule[Label, Expr](Nil, { (subs: Seq[Expr]) => builder }, tag, cost)
  }

  /** Generates a [[ProductionRule]] with nonterminal symbols */
  def nonTerminal(subs: Seq[Label], builder: (Seq[Expr] => Expr), tag: Tags.Tag = Tags.Top, cost: Int = 1) = {
    ProductionRule[Label, Expr](subs, builder, tag, cost)
  }

  /** The list of production rules for this grammar for a given nonterminal.
    * This is the cached version of [[getProductions]] which clients should use.
    *
    * @param lab The nonterminal for which production rules will be generated
    */
  def getProductions(lab: Label)(implicit ctx: LeonContext): Seq[Prod] = {
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
  def computeProductions(lab: Label)(implicit ctx: LeonContext): Seq[Prod]

  def filter(f: Prod => Boolean) = {
    new ExpressionGrammar {
      def computeProductions(lab: Label)(implicit ctx: LeonContext) = {
        ExpressionGrammar.this.computeProductions(lab).filter(f)
      }
    }
  }

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
