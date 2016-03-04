/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package grammars
package transformers

import purescala.Expressions.Expr
import purescala.ExprOps.formulaSize
import purescala.Types.TypeTree
import purescala.TypeOps.isSubtypeOf

/** Generates one production rule for each expression in a sequence that has compatible type */
case class OneOf(exprs: Seq[Expr]) extends ExpressionGrammar {
  lazy val prods = {
    exprs.map { e =>
      val c = formulaSize(e)
      Label(e.getType, c) -> terminal(e, Tags.Top, c)
    }
  }.groupBy(_._1).mapValues(_ map (_._2))

  def computeProductions(l: Label)(implicit ctx: LeonContext): Seq[Prod] = {
    prods.getOrElse(l, Nil)
  }
}
