/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package synthesis
package rules

import solvers.TimeoutSolver
import purescala.Trees._
import purescala.TypeTrees._
import purescala.TreeOps._
import purescala.Extractors._

case object ChooseCloser extends Rule("ChooseCloser") {
  def instantiateOn(sctx: SynthesisContext, p: Problem): Traversable[RuleInstantiation] = {
    val sol = Solution.choose(p)
    Some(RuleInstantiation.immediateSuccess(p, this, sol))
  }
}

