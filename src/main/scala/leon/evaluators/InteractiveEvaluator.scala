/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package evaluators

import synthesis.ConvertWithOracle
import purescala.Common._
import purescala.Trees._
import purescala.Definitions._
import purescala.TreeOps._
import purescala.TypeTrees._
import solvers.z3._
import solvers._

class InteractiveEvaluator(ctx: LeonContext, prog: Program) extends RecursiveEvaluator(ctx, prog) {
  type RC = DefaultRecContext
  type GC = InteractiveGlobalContext

  var lastGlobalContext: Option[GC] = None

  def initRC(mappings: Map[Identifier, Expr]) = DefaultRecContext(mappings)
  def initGC = {
    val gc = new InteractiveGlobalContext(stepsLeft = 50000, Map())
    lastGlobalContext = Some(gc)
    gc
  }

  case class DefaultRecContext(mappings: Map[Identifier, Expr]) extends RecContext {
    def withNewVar(id: Identifier, v: Expr) = copy(mappings + (id -> v))
    def withVars(news: Map[Identifier, Expr]) = copy(news)
  }

  class InteractiveGlobalContext(stepsLeft: Int, var tests: Map[Identifier, List[(List[Expr], Expr)]]) extends GlobalContext(stepsLeft)

  class InteractiveOracle(id: Identifier) {
    val AbstractClassType(_, List(tpe)) = id.getType

    def indent(implicit ind: Int) = {
      "  "*ind
    }

    def ask[T](tpe: String, convert: String => Option[T])(implicit ind: Int): T = {
      var res: Option[T] = None
      do {
          print(indent+"Requesting value for "+tpe+": ")
          res = try {
            convert(readLine())
          } catch {
            case e: Throwable =>
              None
          }
          if (res.isEmpty) {
            println(indent+"Unable to extract "+tpe+".")
          }
      } while(res.isEmpty)

      res.get
    }

    def askAlternatives[T](alts: Seq[T], printer: T => String)(implicit ind: Int): T = {
      var res: Option[T] = None
      do {
          println(indent+"Alternatives: ")
          alts.zipWithIndex.foreach { case (a, i) =>
            println(indent+"  "+(i+1)+": "+printer(a))
          }

          val i = try {
            print(indent+">")
            readLine().toInt
          } catch {
            case e: Throwable =>
              0
          }

          if (i <= 0 || i > alts.size) {
            println(indent+"?")
          } else {
            res = Some(alts(i-1))
          }
      } while(res.isEmpty)

      res.get
    }

    def produceValueFor(tpe: TypeTree)(implicit ind: Int = 0): Expr = tpe match {
      case Int32Type =>
        ask("Integer", s => Some(IntLiteral(s.toInt)))

      case BooleanType =>
        ask("boolean", _ match {
          case "true" | "" => Some(BooleanLiteral(true))
          case "false"     => Some(BooleanLiteral(false))
          case _           => None
        })

      case SetType(base) =>
        val s = ask("Set size?", s => Some(s.toInt))

        val elems = for (i <- 1 to s) yield {
          produceValueFor(base)(ind+1)
        }

        FiniteSet(elems).setType(SetType(base))


      case act: AbstractClassType =>
        val alternatives = act.knownCCDescendents
        val cct = askAlternatives(alternatives, { (cct: CaseClassType) => cct.toString })
        produceValueFor(cct)

      case cct: CaseClassType =>
        val exs = cct.fieldsTypes.foldLeft(Nil: List[Expr]){
          (prev, t) =>
            val args = (prev.map(_.toString) ::: "?" :: Nil).padTo(cct.fields.size, "")

            println(indent+cct+"("+args.mkString(", ")+")")

            prev ::: produceValueFor(t)(ind+1) :: Nil
        }
        CaseClass(cct, exs)

      case _ =>
        throw new EvalError("Unable to produce witness for "+tpe)
    }

    lazy val head: Expr = produceValueFor(tpe)

    lazy val left: Expr  = new ExternalObject(new InteractiveOracle(id), id.getType)
    lazy val right: Expr = new ExternalObject(new InteractiveOracle(id), id.getType)
  }

  def yesOrNo(ask: String): Boolean = {
    var res: Option[Boolean] = None
    while(res.isEmpty) {
      println(ask+" [y]es/[n]o")
      readLine() match {
        case "" | "yes" | "y" => res = Some(true)
        case "no" | "n"  => res = Some(false)
        case _ =>
          println("?")
      }
    }
    res.get
  }

  def explanationSimplifier(e: Expr): Expr = {
    val uninterpretedZ3 = SolverFactory(() => new UninterpretedZ3Solver(ctx, prog))

    val simplifiers = List[Expr => Expr](
      simplifyTautologies(uninterpretedZ3)(_),
      simplifyLets _,
      decomposeIfs _,
      matchToIfThenElse _,
      simplifyPaths(uninterpretedZ3)(_),
      patternMatchReconstruction _,
      rewriteTuples _,
      evalGround(ctx, prog),
      normalizeExpression _
    )

    val simple = { expr: Expr =>
      simplifiers.foldLeft(expr){ case (x, sim) => 
        sim(x)
      }
    }

    fixpoint(simple, 5)(e)
  }

  override def e(expr: Expr)(implicit rctx: RC, gctx: GC): Expr = {
    expr match {
      case wo @ WithOracle(os, b, true) => // Interactive Oracle

        val Some(Choose(cos, pred)) = ConvertWithOracle.getChoose(wo)

        val instPred = replaceFromIDs(rctx.mappings, pred)

        //println(instPred)
        //println(explanationSimplifier(instPred))

        var last: Option[Expr] = None

        do {
          var allTests = gctx.tests
          gctx.tests = Map()
          try {
            val ios = os.map(o => new ExternalObject(new InteractiveOracle(o), o.getType))
            val res = super.e(LetTuple(os, Tuple(ios), b))
            last = Some(res)

            allTests = (allTests.keySet ++ gctx.tests.keySet).map { k =>
              k -> (allTests.getOrElse(k, Nil) ::: gctx.tests.getOrElse(k, Nil))
            }.toMap
          } catch {
            case RuntimeError(e) =>
              println("Run failed with "+e)
          }
          gctx.tests = allTests
        } while(last.isEmpty)

        last.get

      case fi @ FunctionInvocation(tfd, args) =>
        val rargs = args.map(e)

        (tfd.id.name, rargs) match {
          case ("Oracle.head", List(ExternalObject(io: InteractiveOracle, _))) =>
            io.head

          case ("Oracle.left", List(ExternalObject(io: InteractiveOracle, _))) =>
            io.left

          case ("Oracle.right", List(ExternalObject(io: InteractiveOracle, _))) =>
            io.right

          case _ =>
            val ins = rargs.toList
            val out = super.e(FunctionInvocation(tfd, rargs))

            println("  ; ---- Recorded test for "+tfd.id+": ---")
            println("  ; "+ins.mkString(" :: ")+"   --->  "+out)
            gctx.tests += tfd.id -> ((ins -> out) :: gctx.tests.getOrElse(tfd.id, Nil))

            out

        }
      case _ =>
        super.e(expr)
    }
  }

}
