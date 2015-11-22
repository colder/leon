/* Copyright 2009-2015 EPFL, Lausanne */

package leon.integration.solvers

import leon.test._
import leon.test.helpers._
import leon.purescala.Common._
import leon.purescala.Definitions._
import leon.purescala.ExprOps._
import leon.purescala.Constructors._
import leon.purescala.Expressions._
import leon.purescala.Types._
import leon.LeonContext

import leon.solvers._
import leon.solvers.smtlib._
import leon.solvers.combinators._
import leon.solvers.z3._

class GlobalVariablesSuite extends LeonTestSuiteWithProgram with ExpressionsDSL {

  val sources = List(
    """|import leon.lang._
       |import leon.annotation._
       |
       |object GlobalVariables {
       |
       |  def test(i: BigInt): BigInt = {
       |    test2(i)
       |  }
       |
       |  def test2(i: BigInt): BigInt = {
       |    BigInt(0) // will get replaced
       |  }
       |} """.stripMargin
  )

  val getFactories: Seq[(String, (LeonContext, Program) => Solver)] = {
    (if (SolverFactory.hasNativeZ3) Seq(
      ("fairz3",   (ctx: LeonContext, pgm: Program) => new FairZ3Solver(ctx, pgm))
    ) else Nil) ++
    (if (SolverFactory.hasZ3)       Seq(
      ("smt-z3",   (ctx: LeonContext, pgm: Program) => new UnrollingSolver(ctx, pgm, new SMTLIBZ3Solver(ctx, pgm)))
    ) else Nil) ++
    (if (SolverFactory.hasCVC4)     Seq(
      ("smt-cvc4", (ctx: LeonContext, pgm: Program) => new UnrollingSolver(ctx, pgm, new SMTLIBCVC4Solver(ctx, pgm)))
    ) else Nil)
  }

  // Check that we correctly extract several types from solver models
  for ((sname, sf) <- getFactories) {
    test(s"Global Variables in $sname") { implicit fix =>
      val ctx = fix._1
      val pgm = fix._2

      pgm.lookup("GlobalVariables.test2") match {
        case Some(fd: FunDef) =>
          val solver = sf(ctx, pgm)
          val b0 = FreshIdentifier("B", BooleanType);
          fd.body = Some(IfExpr(b0.toVariable, bi(1), bi(-1)))

          pgm.lookup("GlobalVariables.test") match {
            case Some(fd: FunDef) =>

              val cnstr = LessThan(FunctionInvocation(fd.typed, Seq(bi(42))), bi(0))
              val solver = sf(ctx, pgm)
              solver.assertCnstr(b0.toVariable)
              solver.assertCnstr(cnstr)

              if (solver.check != Some(false)) {
                fail("Global variables not correctly handled.")
              }
            case _ =>
              fail("Entry point not found!")
          }
        case _ =>
          fail("Function with global body not found")
      }

    }
  }
}
