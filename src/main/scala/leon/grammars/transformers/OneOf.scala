/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package grammars
package transformers

import purescala.Expressions.Expr
import purescala.ExprOps.formulaSize
import purescala.Types.TypeTree
import purescala.TypeOps.isSubtypeOf

/** Generates one production rule for each expression in a sequence that has compatible type */
case class OneOf(exprs: Seq[Expr]) extends SimpleExpressionGrammar {

  def computeProductions(tpe: TypeTree)(implicit ctx: LeonContext): Seq[Prod] = {
    exprs.collect {
      case e if isSubtypeOf(e.getType, tpe) =>
        terminal(e, cost = formulaSize(e))
    }
  }
}
