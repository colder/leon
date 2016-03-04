/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package grammars
package transformers

import purescala.Types.Typed
import utils.SeqUtils._

///** Adds information about size to a nonterminal symbol */
//case class SizedNonTerm[T <: Typed](underlying: T, size: Int) extends Typed {
//  val getType = underlying.getType
//
//  override def asString(implicit ctx: LeonContext) = underlying.asString+"|"+size+"|"
//}
//
///** Limits a grammar by producing expressions of size bounded by the [[SizedNonTerm.size]] of a given [[SizedNonTerm]].
//  *
//  * In case of commutative operations, the grammar will produce trees skewed to the right
//  * (i.e. the right subtree will always be larger). Notice we do not lose generality in case of
//  * commutative operations.
//  */
//case class SizeBoundedGrammar[T <: Typed](g: ExpressionGrammar[T], optimizeCommut: Boolean) extends ExpressionGrammar[SizedNonTerm[T]] {
//  def computeProductions(sl: SizedNonTerm[T])(implicit ctx: LeonContext): Seq[Prod] = {
//  }
//}
