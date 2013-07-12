/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package solvers

import purescala.Common._
import purescala.Definitions._
import purescala.TreeOps._
import purescala.Trees._

trait ProofGeneratingSolver {
  // TODO: Proofs are more complex than Leon Expr, for now return Expr
  def getProof: Option[Expr]
}

trait ProofGeneratingSolverBuilder {
  self: IncrementalSolverBuilder =>

  def getNewSolver: IncrementalSolver with ProofGeneratingSolver
}

