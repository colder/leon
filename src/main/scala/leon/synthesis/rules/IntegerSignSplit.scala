/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package synthesis
package rules

import purescala.Trees._
import purescala.Common._
import purescala.TypeTrees._
import purescala.TreeOps._
import purescala.Extractors._

case object IntegerSignSplit extends Rule("Sign Split") {

  def instantiateOn(sctx: SynthesisContext, p: Problem): Traversable[RuleInstantiation] = {
    val solver = sctx.simpleSolver

    val candidates = p.as.collect {
      case IsTyped(i, Int32Type) =>
        i
    }


    candidates.flatMap(_ match {
      case i =>

        val sub1 = p.copy(pc = And(Equals(Variable(i), IntLiteral(0)), p.pc))
        val sub2 = p.copy(pc = And(LessThan(Variable(i), IntLiteral(0)), p.pc))
        val sub3 = p.copy(pc = And(GreaterThan(Variable(i), IntLiteral(0)), p.pc))

        val onSuccess: List[Solution] => Option[Solution] = {
          case List(s1, s2, s3) =>
            Some(Solution(
                Or(Seq(s1.pre, s2.pre, s3.pre)),
                s1.defs++s2.defs++s3.defs,
                  IfExpr(Equals(Variable(i), IntLiteral(0)),
                    s1.term,
                    IfExpr(LessThan(Variable(i), IntLiteral(0)),
                      s2.term,
                      s3.term))))
          case _ =>
            None
        }

        Some(RuleInstantiation.immediateDecomp(p, this, List(sub1, sub2, sub3), onSuccess, "Sign Split on '"+i+"'"))
    })
  }
}
