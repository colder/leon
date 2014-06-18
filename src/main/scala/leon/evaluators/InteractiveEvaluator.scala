/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package evaluators

import synthesis.ConvertWithOracle
import purescala.Common._
import purescala.ScalaPrinter
import purescala.Trees._
import purescala.Definitions._
import purescala.TreeOps._
import purescala.TypeTrees._
import solvers.z3._
import solvers._
import utils.ConsoleUtils
import synthesis._

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

  class InteractiveGlobalContext(stepsLeft: Int, var tests: Map[FunDef, Map[List[Expr], Expr]]) extends GlobalContext(stepsLeft) {
  }

  class InteractiveOracle(id: Identifier) {
    import ConsoleUtils._

    val AbstractClassType(_, List(tpe)) = id.getType

    def produceValueFor(tpe: TypeTree): Expr = tpe match {
      case Int32Type =>
        ask("Int value: ", s => Some(IntLiteral(s.toInt)))

      case BooleanType =>
        ask("Boolean value: ", _ match {
          case "true" | "" => Some(BooleanLiteral(true))
          case "false"     => Some(BooleanLiteral(false))
          case _           => None
        })

      case SetType(base) =>
        val s = ask("Set size: ", s => Some(s.toInt))

        val elems = for (i <- 1 to s) yield {
          produceValueFor(base)
        }

        FiniteSet(elems).setType(SetType(base))


      case act: AbstractClassType =>
        val alternatives = act.knownCCDescendents
        val cct = askAlternatives("Choose a constructor: ", alternatives, { (cct: CaseClassType) => cct.toString })
        produceValueFor(cct)

      case cct: CaseClassType =>
        val exs = cct.fieldsTypes.foldLeft(Nil: List[Expr]){
          (prev, t) =>
            val args = (prev.map(_.toString) ::: "?" :: Nil).padTo(cct.fields.size, "")

            println(cct+"("+args.mkString(", ")+")")

            prev ::: produceValueFor(t) :: Nil
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

  def isOracleType(t: TypeTree): Boolean = t match {
    case (ct: ClassType) => ct.classDef.id.name == "Oracle"
    case _ => false
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
          // We temporarily save the state of tests, so that if new tests are
          // recorded within a erroneous execution, they can be ignored.
          var allTests = gctx.tests
          gctx.tests = Map()
          try {
            val ios = os.map(o => new ExternalObject(new InteractiveOracle(o), o.getType))
            val res = super.e(LetTuple(os, Tuple(ios), b))
            last = Some(res)

            allTests = (allTests.keySet ++ gctx.tests.keySet).map { k =>
              k -> (allTests.getOrElse(k, Map()) ++ gctx.tests.getOrElse(k, Map()))
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
            val out = super.e(FunctionInvocation(tfd, rargs))

            if (rargs.exists(a => isOracleType(a.getType))) {
              val ins = rargs.toList.filter(a => !isOracleType(a.getType))
              gctx.tests += tfd.fd -> (gctx.tests.getOrElse(tfd.fd, Map()) + (ins -> out))
            }

            out

        }
      case _ =>
        super.e(expr)
    }
  }

  def getRecordedTests: Map[FunDef, Map[List[Expr], Expr]] = {
      lastGlobalContext.map(_.tests).getOrElse(Map())
  }

  def oracleCalls(fd: FunDef): Set[FunctionInvocation] = {
    fd.body.map(collect[FunctionInvocation]{
      case fi @ FunctionInvocation(tfd, args) if tfd.id.name == "Oracle.head" => Set(fi)
      case _ => Set()
    }).getOrElse(Set())
  }

  def printRecordedTests() {
    import leon.utils.ASCIITables._
    for ((fd, ts) <- getRecordedTests) {
      var tbl = new Table("Tests of "+fd.id.name)

      val params = fd.params.toList.filter(p => !isOracleType(p.getType))
      tbl += Row(params.map(p => Cell(p.id.name)) ::: Cell("=>") :: Cell("ret") :: Nil)
      tbl += Separator
      for ((ins, out) <- ts) {
        tbl += Row(ins.map(i => Cell(i)) ::: Cell("=>") :: Cell(out) :: Nil)
      }

      println(tbl.render)
    }
  }

  def synthesizeFromTests() {
    for ((fd, tests) <- getRecordedTests) {
      val ocs = oracleCalls(fd)

      if (ocs.nonEmpty) {
        println("Synthesizing "+fd.id)

        val (as, os) = fd.params.partition(p => !isOracleType(p.getType))

        assert(os.size == 1, "Only support one oracle for now")

        val nfd = new FunDef(fd.id.freshen, fd.tparams, fd.returnType, as)
        val (pid, post) = fd.postcondition.getOrElse((FreshIdentifier("res").setType(fd.returnType), BooleanLiteral(true)))

        val wopost = tests.foldLeft(BooleanLiteral(true): Expr){ case (e, (ins,out)) =>
          IfExpr(And((as zip ins).map(a => Equals(a._1.id.toVariable, a._2))), Equals(Variable(pid), out), e)
        }
        val wobody = withPostcondition(fd.body.get, Some((pid, wopost)))
        val wo = WithOracle(os.map(_.id).toList, wobody, false)

        nfd.fullBody = withBody(fd.fullBody, Some(wo))

        ConvertWithOracle.getChoose(wo) match {
          case Some(ch) =>
            val p = Problem.fromChoose(ch)
            val s = new Synthesizer(ctx, Some(nfd), prog, p, SynthesisOptions(manualSearch = true))
            println(p)
            readLine()
            val res = s.synthesize()
            println(res)
          case None =>

        }
      }
    }
  }

  override def eval(ex: Expr, mappings: Map[Identifier, Expr]) = {
    var last: Option[EvaluationResult] = None
    do {
      last = Some(super.eval(ex, mappings))

      printRecordedTests()
      synthesizeFromTests()

    } while(yesOrNo("Run again?"))

    last.get
  }

}
