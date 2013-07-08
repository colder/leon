package leon
package synthesis
package runtime

import purescala.Definitions._
import purescala.Common.UniqueCounter
import purescala.TreeOps.replace
import solvers.{Solver, TimeoutSolver, IncrementalSolver}
import solvers.z3.FairZ3Solver
import java.io.{File, FileInputStream, ObjectInputStream}

object RuntimeSynthesis {
  private[this] var initialized               = false
  private[this] var program: Program          = null
  private[this] var ctx: LeonContext          = null
  private[this] var options: SynthesisOptions = null
  private[this] var mainSolver: Solver        = null

  import purescala.Trees._

  def init(fileName: String) {
    val ois = new ObjectInputStream(new FileInputStream(new File(fileName)))
    program = ois.readObject().asInstanceOf[Program]
    val cnt = ois.readObject().asInstanceOf[Int]
    ois.close

    UniqueCounter.reset(cnt)


    val opts    = List(
//                    LeonFlagOption("codegen"),
//                    LeonFlagOption("feelinglucky"),
//                    LeonFlagOption("evalground")
//                    LeonFlagOption("fairz3:unrollcores")
                  )

    ctx         = LeonContext(options = opts)
    options     = SynthesisOptions()
    val fair    = new FairZ3Solver(ctx.copy(reporter = new SilentReporter()))
    fair.setProgram(program)
    mainSolver  = new TimeoutSolver(fair, 60000L) // We give that 1min
  }

  object ExCaseClass {
    def unapply(r: AnyRef): Option[CaseClassDef] = {
      r.getClass.getName.split("\\$").toSeq match {
        case Seq(mainObj, name) if mainObj == program.mainObject.id.name =>
          try {
            Some(program.mainObject.caseClassDef(name))
          } catch {
            case _: Throwable =>
              None
          }
        case _ =>
          None
      }
    }
  }

  def classOf(ccd: CaseClassDef): Class[_] = {
      val javaClassName = if (ccd.isCaseObject) {
        program.mainObject.id.name+"$"+ccd.id.name+"$"
      } else {
        program.mainObject.id.name+"$"+ccd.id.name
      }

      Class.forName(javaClassName)
  }

  def leonValtoVal(v: Expr): Any =  v match {
    case IntLiteral(i) =>
      i
    case StringLiteral(s) =>
      s
    case BooleanLiteral(b) =>
      b
    case UnitLiteral =>
      ()

    case CaseClass(ccd, args) =>
      if (ccd.isCaseObject) {
        classOf(ccd).getConstructor().newInstance()
      } else {
        val cl = classOf(ccd)
        val valArgs = args.map(leonValtoVal).asInstanceOf[Seq[AnyRef]]
        classOf(ccd).getDeclaredConstructors()(0).newInstance(valArgs : _ *)
      }

    case _ =>
      ctx.reporter.fatalError("Unhandled value: "+v+" ("+v.getClass+")")
  }

  def valToLeonVal(v: Any): Expr =  v match {
    case i: Int =>
      IntLiteral(i)
    case s: String =>
      StringLiteral(s)
    case b: Boolean =>
      BooleanLiteral(b)
    case () =>
      UnitLiteral

    case r @ ExCaseClass(ccd) =>
      val cl = r.getClass

      val args = for (f <- ccd.fieldsIds) yield {
        valToLeonVal(cl.getDeclaredMethod(f.name).invoke(r))
      }
      CaseClass(ccd, args)

    case s : Set[_] =>
      FiniteSet(s.toSeq.map(valToLeonVal))

    case _ =>
      ctx.reporter.fatalError("Unhandled value: "+v+" ("+v.getClass+")")
  }

  def onChoose(fileName: String, line: Int, inputs: Map[String, Any]): Any = {
    val tStart = System.currentTimeMillis
    if (!initialized) {
      init(fileName);
    }

    var chooses = ChooseInfo.extractFromProgram(ctx, program, options)

    chooses.find(_.ch.posIntInfo._1 == line) match {
      case Some(ci) =>
        ctx.reporter.info("Starting runtime synthesis on "+ci.ch+" with: "+inputs+"...")
        val p = ci.problem

        val as = p.as.map(i => i.name -> i).toMap

        val inputsMap = inputs.map {
          case (name, v) =>
            (Variable(as(name)): Expr) -> valToLeonVal(v)
        }


        val newPhi = replace(inputsMap, p.phi)

        val solver = mainSolver.getNewSolver
        solver.assertCnstr(newPhi)
        println(newPhi)

        solver.check match {
          case Some(true) =>
            val model = solver.getModel;

            val res = p.xs.map(model(_))
            val leonRes = if (res.size > 1) {
              Tuple(res)
            } else {
              res(0)
            }

            val total = System.currentTimeMillis-tStart;
            ctx.reporter.info("Synthesis took "+total+"ms")

            ctx.reporter.info("Finished synthesis with "+leonRes)

            leonValtoVal(leonRes)
          case Some(false) =>
            sys.error("UNSAT")
          case _ =>
            sys.error("TIMEOUT")

        }

      case None =>
        ctx.reporter.fatalError("Woops. Choose not found.")
    }
  }
}
