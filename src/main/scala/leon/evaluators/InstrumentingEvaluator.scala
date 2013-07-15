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

class VanuatooContext(val unit : CompilationUnit, val ctx: LeonContext) {

  val ints = (for (i <- Set(0, 1, 2, 3)) yield {
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

  def getGeneratorFor(t: CaseClassType, act: AbstractClassType): Constructor[Expr, TypeTree] = {
    // We "up-cast" the returnType of the specific caseclass generator to match its superclass
    getGenerator(t)(0).copy(retType = act)
  }


  def getGenerator(t: TypeTree): List[Constructor[Expr, TypeTree]] = t match {
    case tt @ TupleType(parts) =>
      List(tConstructors.getOrElse(tt, {
        val c = Constructor[Expr, TypeTree](parts, tt, s => Tuple(s).setType(tt), tt.toString)
        tConstructors += tt -> c
        c
      }))

    case act @ AbstractClassType(acd) =>
      acConstructors.getOrElse(acd, {
        val cs = acd.knownDescendents.collect {
          case ccd: CaseClassDef =>
            getGeneratorFor(CaseClassType(ccd), act)
        }.toList

        acConstructors += acd -> cs

        cs
      })

    case CaseClassType(ccd) =>
      List(ccConstructors.getOrElse(ccd, {
        val c = Constructor[Expr, TypeTree](ccd.fields.map(_.tpe), CaseClassType(ccd), s => CaseClass(ccd, s), ccd.id.name)
        ccConstructors += ccd -> c
        c
      }))

    case _ =>
      ctx.reporter.error("Unknown type to generate constructor for: "+t)
      Nil
  }

  def valueToPattern(v: AnyRef, expType: TypeTree): VPattern[Expr, TypeTree] = (v, expType) match {
    case (i: Integer, Int32Type) =>
      cPattern(intConstructor(i), List())

    case (b: java.lang.Boolean, BooleanType) =>
      cPattern(boolConstructor(b), List())

    case (cc: codegen.runtime.CaseClass, ct: ClassType) =>
      val r = cc.__getRead()

      unit.jvmClassToDef.get(cc.getClass.getName) match {
        case Some(ccd: CaseClassDef) =>
          val c = ct match {
            case act : AbstractClassType =>
              getGeneratorFor(CaseClassType(ccd), act)
            case cct : CaseClassType =>
              getGenerator(CaseClassType(ccd))(0)
          }

          val fields = cc.productElements()

          val elems = for (i <- 0 until fields.length) yield {
            if (((r >> i) & 1) == 1) {
              // has been read
              valueToPattern(fields(i), ccd.fieldsIds(i).getType)
            } else {
              AnyPattern[Expr, TypeTree]()
            }
          }

          ConstructorPattern(c, elems)

        case _ =>
          sys.error("Could not retreive type for :"+cc.getClass.getName)
      }

    case (t: codegen.runtime.Tuple, tt @ TupleType(parts)) =>
      val r = t.__getRead()

      val c = getGenerator(tt)(0)

      val elems = for (i <- 0 until t.getArity) yield {
        if (((r >> i) & 1) == 1) {
          // has been read
          valueToPattern(t.get(i), parts(i))
        } else {
          AnyPattern[Expr, TypeTree]()
        }
      }

      ConstructorPattern(c, elems)

    case _ =>
      sys.error("Unsupported value, can't paternify : "+v+" : "+expType)
  }

  def mkGenerator = {
    new StubGenerator[Expr, TypeTree](allConstructors, Some(getGenerator _))
  }
}

class VanuatooModelFinder(ctx: LeonContext, p: Program) {
  def findModels(e: Expr, argorder: Seq[Identifier], maxValid: Int, maxEnumerated: Int): Seq[Seq[Expr]] = {
    val vctx = new VanuatooContext(CompilationUnit.compileProgram(p).get, ctx)
    val instrEval = new InstrumentingEvaluator(vctx)

    instrEval.compile(e, argorder) match {
      case Some(runner) =>
        var found = Set[Seq[Expr]]()

        val gen = vctx.mkGenerator
        val it  = gen.enumerate(TupleType(argorder.map(_.getType)))

        var c = 0

        while (c < maxEnumerated && found.size < maxValid && it.hasNext) {
          val model = it.next.asInstanceOf[Tuple]


          if (model eq null) {
            c = maxEnumerated
          } else {
            runner(model) match {
              case (EvaluationResults.Successful(BooleanLiteral(true)), _) =>
                //println("Got model "+model)

                found += model.exprs

              case (_, Some(pattern)) =>
                //println("From model: "+model)
                //println("Got pattern to exclude "+pattern)

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


class InstrumentingEvaluator(vctx: VanuatooContext) {

  type InstrumentedResult = (EvaluationResults.Result, Option[vanuatoo.Pattern[Expr, TypeTree]])

  def compile(expression : Expr, argorder : Seq[Identifier]) : Option[Tuple=>InstrumentedResult] = {
    import leon.codegen.runtime.LeonCodeGenRuntimeException
    import leon.codegen.runtime.LeonCodeGenEvaluationException

    try {
      val ttype = TupleType(argorder.map(_.getType))
      val tid = FreshIdentifier("tup").setType(ttype)

      val map = argorder.zipWithIndex.map{ case (id, i) => (id -> TupleSelect(Variable(tid), i+1)) }.toMap

      val newExpr = replaceFromIDs(map, expression)

      val ce = vctx.unit.compileExpression(newExpr, Seq(tid))

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
        vctx.ctx.reporter.warning("Error while compiling expression: "+t.getMessage)
        None
    }
  }
}
