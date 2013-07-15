/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package evaluators

import purescala.Common._
import purescala.Definitions._
import purescala.TreeOps._
import purescala.Trees._
import purescala.TypeTrees._

import codegen.CompilationUnit
import vanuatoo.{Pattern => VPattern, _}

class VanuatooContext(ctx: LeonContext) {

  val ints = (for (i <- Set(0,1,2,3)) yield {
    i -> Constructor[Expr, TypeTree](List(), Int32Type, s => IntLiteral(i), ""+i)
  }).toMap

  val booleans = (for (b <- Set(true, false)) yield {
    b -> Constructor[Expr, TypeTree](List(), BooleanType, s => BooleanLiteral(b), ""+b)
  }).toMap

  def intConstructor(i: Int) = ints(i)

  def boolConstructor(b: Boolean) = booleans(b)

  def cPattern(c: Constructor[Expr, TypeTree], args: Seq[VPattern[Expr, TypeTree]]) = {
    ConstructorPattern[Expr, TypeTree](c, args)
  }

  var ccConstructors = Map[CaseClassDef, Constructor[Expr, TypeTree]]()
  var acConstructors = Map[AbstractClassDef, List[Constructor[Expr, TypeTree]]]()
  var tConstructors  = Map[TupleType, Constructor[Expr, TypeTree]]()

  def allConstructors: List[Constructor[Expr, TypeTree]] = {
    (ints.values ++ booleans.values ++ ccConstructors.values ++ acConstructors.flatMap(_._2) ++ tConstructors.values).toList
  }

  def constrGenerator(t: TypeTree): List[Constructor[Expr, TypeTree]] = {
    println("I got asked for constructors for "+t)
    val res = t match {
      case tt @ TupleType(parts) =>
        List(tConstructors.getOrElse(tt, {
          val c = Constructor[Expr, TypeTree](parts, tt, s => Tuple(s).setType(tt), "tt")
          tConstructors += tt -> c
          c
        }))

      case AbstractClassType(acd) =>
        acConstructors.getOrElse(acd, {
          val cs = acd.knownDescendents.collect {
            case ccd: CaseClassDef =>
              constrGenerator(CaseClassType(ccd))(0)
          }.toList

          acConstructors += acd -> cs

          cs
        })

      case CaseClassType(ccd) =>
        List(ccConstructors.getOrElse(ccd, {
          val c = Constructor[Expr, TypeTree](ccd.fields.map(_.tpe), CaseClassType(ccd), s => CaseClass(ccd, s), ccd.toString)
          ccConstructors += ccd -> c
          c
        }))

      case _ =>
        ctx.reporter.error("Unknown type to generate constructor for: "+t)
        Nil
    }
    println("I got "+res)
    res
  }

  def valueToPattern(v: AnyRef, expType: TypeTree): VPattern[Expr, TypeTree] = (v, expType) match {
    case (i: Integer, Int32Type) =>
      cPattern(intConstructor(i), List())

    case (b: java.lang.Boolean, BooleanType) =>
      cPattern(boolConstructor(b), List())

    case (cc: codegen.runtime.CaseClass, _: ClassType) =>
      val r = cc.__getRead()

      println("GOT READ: "+Integer.toBinaryString(r))

      null

    case (t: codegen.runtime.Tuple, TupleType(parts)) =>
      val r = t.__getRead()

      println("GOT READ: "+Integer.toBinaryString(r))

      null

    case _ =>
      sys.error("Unsupported value, can't paternify : "+v+" : "+expType)
  }

  def mkGenerator = {
    new StubGenerator[Expr, TypeTree](allConstructors, Some(constrGenerator _))
  }
}

class VanuatooModelFinder(ctx: LeonContext, p: Program) {
  def findModels(e: Expr, argorder: Seq[Identifier], maxValid: Int, maxEnumerated: Int): Seq[Seq[Expr]] = {
    val vctx = new VanuatooContext(ctx)
    val instrEval = new InstrumentingEvaluator(ctx, p, vctx)

    instrEval.compile(e, argorder) match {
      case Some(runner) =>

        println("Compiled, ready to run..")

        var found = Set[Seq[Expr]]()

        println(argorder.map(_.getType))

        val gen = vctx.mkGenerator

        println("I HAS A GENERATOAR!")

        val it  = gen.enumerate(TupleType(argorder.map(_.getType)))

        println("I HAS AN ITERATOR!")

        var c = 0

        while (c < maxEnumerated && found.size < maxValid && it.hasNext) {
          val model = it.next.asInstanceOf[Tuple]

          println("Got model "+model)

          if (model eq null) {
            c = maxEnumerated
          } else {
            runner(model) match {
              case (EvaluationResults.Successful(BooleanLiteral(true)), _) =>
                found += model.exprs

              case (_, Some(pattern)) =>
                it.exclude(pattern)

              case _ =>
            }

            c += 1
          }
        }

        found.toSeq
      case None =>
        Seq()
    }
  }
}


class InstrumentingEvaluator(ctx : LeonContext, val unit : CompilationUnit, vctx: VanuatooContext) {

  def this(ctx : LeonContext, prog : Program, vctx: VanuatooContext) {
    this(ctx, CompilationUnit.compileProgram(prog).get, vctx) // this .get is dubious...
  }

  type InstrumentedResult = (EvaluationResults.Result, Option[vanuatoo.Pattern[Expr, TypeTree]])

  def compile(expression : Expr, argorder : Seq[Identifier]) : Option[Tuple=>InstrumentedResult] = {
    import leon.codegen.runtime.LeonCodeGenRuntimeException
    import leon.codegen.runtime.LeonCodeGenEvaluationException

    try {
      val ttype = TupleType(argorder.map(_.getType))
      val tid = FreshIdentifier("tup").setType(ttype)

      val map = argorder.zipWithIndex.map{ case (id, i) => (id -> TupleSelect(Variable(tid), i+1)) }.toMap

      val newExpr = replaceFromIDs(map, expression)

      val ce = unit.compileExpression(newExpr, Seq(tid))

      Some((args : Tuple) => {
        try {
          val jvmArgs = ce.argsToJVM(Seq(args))

          val result  = ce.evalFromJVM(jvmArgs)

          // jvmArgs is getting updated by evaluating
          val pattern = vctx.valueToPattern(jvmArgs(0), ttype)

          (EvaluationResults.Successful(result), Some(pattern))
        } catch {
          case e : ArithmeticException =>
            (EvaluationResults.RuntimeError(e.getMessage), None)

          case e : ArrayIndexOutOfBoundsException =>
            (EvaluationResults.RuntimeError(e.getMessage), None)

          case e : LeonCodeGenRuntimeException =>
            (EvaluationResults.RuntimeError(e.getMessage), None)

          case e : LeonCodeGenEvaluationException =>
            (EvaluationResults.EvaluatorError(e.getMessage), None)
        }
      })
    } catch {
      case t: Throwable =>
        ctx.reporter.warning("Error while compiling expression: "+t.getMessage)
        None
    }
  }
}
