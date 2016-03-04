/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package grammars

import purescala.Types.Typed

/** The empty expression grammar */
case class Empty() extends ExpressionGrammar {
  def computeProductions(l: Label)(implicit ctx: LeonContext) = Nil
}
