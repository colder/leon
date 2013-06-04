/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package plugin

import scala.tools.nsc._
import scala.tools.nsc.plugins._

import purescala.Definitions._
import purescala.Trees._
import xlang.Trees.{Block => PBlock, _}
import xlang.TreeOps._
import purescala.TypeTrees._
import purescala.Common._
import purescala.TreeOps._

trait CodeExtraction extends Extractors {
  self: LeonExtraction =>

  import global._
  import global.definitions._
  import StructuralExtractors._
  import ExpressionExtractors._
  import ExtractorHelpers._


  private lazy val setTraitSym = definitions.getClass("scala.collection.immutable.Set")
  private lazy val mapTraitSym = definitions.getClass("scala.collection.immutable.Map")
  private lazy val multisetTraitSym = try {
    definitions.getClass("scala.collection.immutable.Multiset")
  } catch {
    case _ => null
  }
  private lazy val optionClassSym     = definitions.getClass("scala.Option")
  private lazy val someClassSym       = definitions.getClass("scala.Some")
  private lazy val function1TraitSym  = definitions.getClass("scala.Function1")

  private lazy val arraySym           = definitions.getClass("scala.Array")

  def isArrayClassSym(sym: Symbol): Boolean = sym == arraySym

  def isTuple2(sym : Symbol) : Boolean = sym == tuple2Sym
  def isTuple3(sym : Symbol) : Boolean = sym == tuple3Sym
  def isTuple4(sym : Symbol) : Boolean = sym == tuple4Sym
  def isTuple5(sym : Symbol) : Boolean = sym == tuple5Sym

  def isSetTraitSym(sym : Symbol) : Boolean = {
    sym == setTraitSym || sym.tpe.toString.startsWith("scala.Predef.Set")
  }

  def isMapTraitSym(sym : Symbol) : Boolean = {
    sym == mapTraitSym || sym.tpe.toString.startsWith("scala.Predef.Map")
  }

  def isMultisetTraitSym(sym : Symbol) : Boolean = {
    sym == multisetTraitSym
  }

  def isOptionClassSym(sym : Symbol) : Boolean = {
    sym == optionClassSym || sym == someClassSym
  }

  def isFunction1TraitSym(sym : Symbol) : Boolean = {
    sym == function1TraitSym
  }

  class Extraction(unit: CompilationUnit) {
    def toPureScala(tree: Tree): Option[Expr] = {
      try {
        Some(scala2PureScala(unit)(tree))
      } catch {
        case e: ImpureCodeEncounteredException =>
          None
      }
    }

    def toPureScalaType(typeTree: Type): purescala.TypeTrees.TypeTree = {
      try {
        scalaType2PureScala(unit)(typeTree)
      } catch {
        case e: ImpureCodeEncounteredException =>
          Untyped
      }
    }

    private def extractTopLevelDef: Option[ObjectDef] = {
      unit.body match {
        case p @ PackageDef(name, lst) if lst.size == 0 =>
          reporter.error(p.pos, "No top-level definition found.")
          None

        case PackageDef(name, lst) =>
          if (lst.size > 1) {
            reporter.error(lst(1).pos, "More than one top-level object. Rest will be ignored.")
          }
          lst(0) match {
            case ExObjectDef(n, templ) =>
              Some(extractObjectDef(n.toString, templ))

            case other @ _ =>
              reporter.error(other.pos, "Expected: top-level single object.")
              None
          }
        }
    }

    private def extractObjectDef(nameStr: String, tmpl: Template): ObjectDef = {
      // we assume that the template actually corresponds to an object
      // definition. Typically it should have been obtained from the proper
      // extractor (ExObjectDef)

      var objectDefs: List[ObjectDef] = Nil
      var funDefs: List[FunDef] = Nil

      var scalaClassSyms  = Map[Symbol,Identifier]()
      var scalaClassArgs  = Map[Symbol,Seq[(String,Tree)]]()
      var scalaClassNames = Set[String]()

      // we need the new type definitions before we can do anything...
      tmpl.body.foreach(t =>
        t match {
          case ExAbstractClass(o2, sym) =>
            if(scalaClassNames.contains(o2)) {
              reporter.error(t.pos, "A class with the same name already exists.")
            } else {
              scalaClassSyms  += sym -> FreshIdentifier(o2)
              scalaClassNames += o2
            }

          case ExCaseClass(o2, sym, args) =>
            if(scalaClassNames.contains(o2)) {
              reporter.error(t.pos, "A class with the same name already exists.")
            } else {
              scalaClassSyms  += sym -> FreshIdentifier(o2)
              scalaClassNames += o2
              scalaClassArgs  += sym -> args
            }

          case _ =>
            reporter.warning(t.pos, "Ignoring top-level construct")
        }
      )

      for ((sym, id) <- scalaClassSyms) {
        if (sym.isAbstractClass) {
          classesToClasses += sym -> new AbstractClassDef(id)
        } else {
          val ccd = new CaseClassDef(id)
          ccd.isCaseObject = sym.isModuleClass
          classesToClasses += sym -> ccd
        }
      }

      for ((sym, ctd) <- classesToClasses) {
        val superClasses: List[ClassTypeDef] = sym.tpe.baseClasses
            .filter(bcs => scalaClassSyms.contains(bcs) && bcs != sym)
            .map(s => classesToClasses(s)).toList


        val superAClasses: List[AbstractClassDef] = superClasses.flatMap {
          case acd: AbstractClassDef =>
            Some(acd)
          case c =>
            reporter.error(sym.pos, "Class "+ctd.id+" is inheriting from non-abstract class "+c.id+".")
            None
        }

        if (superAClasses.size > 2) {
          reporter.error(sym.pos, "Multiple inheritance is not permitted, ignoring extra parents.")
        }

        superAClasses.headOption.foreach{ parent => ctd.setParent(parent) }

        ctd match {
          case ccd: CaseClassDef =>
            assert(scalaClassArgs contains sym)

            ccd.fields = scalaClassArgs(sym).map{ case (name, asym) =>
              val tpe = toPureScalaType(asym.tpe)
              VarDecl(FreshIdentifier(name).setType(tpe), tpe)
            }
          case _ =>
            // no fields to set
        }
      }

      var classDefs: List[ClassTypeDef] = classesToClasses.values.toList

      // we now extract the function signatures.
      tmpl.body.foreach(
        _ match {
          case ExMainFunctionDef() => ;
          case dd @ ExFunctionDef(n,p,t,b) => {
            val mods = dd.mods
            val funDef = extractFunSig(n, p, t).setPosInfo(dd.pos.line, dd.pos.column)
            if(mods.isPrivate) funDef.addAnnotation("private")
            for(a <- dd.symbol.annotations) {
              a.atp.safeToString match {
                case "leon.Annotations.induct" => funDef.addAnnotation("induct")
                case "leon.Annotations.axiomatize" => funDef.addAnnotation("axiomatize")
                case "leon.Annotations.main" => funDef.addAnnotation("main")
                case _ => ;
              }
            }
            defsToDefs += (dd.symbol -> funDef)
          }
          case _ => ;
        }
      )

      // then their bodies.
      tmpl.body.foreach(
        _ match {
          case ExMainFunctionDef() => ;
          case dd @ ExFunctionDef(n,p,t,b) => {
            val fd = defsToDefs(dd.symbol)
            defsToDefs(dd.symbol) = extractFunDef(fd, b)
          }
          case _ => ;
        }
      )

      funDefs = defsToDefs.valuesIterator.toList

      // we check nothing else is polluting the object.
      tmpl.body.foreach(
        _ match {
          case ExCaseClassSyntheticJunk() => ;
          // case ExObjectDef(o2, t2) => { objectDefs = extractObjectDef(o2, t2) :: objectDefs }
          case ExAbstractClass(_,_) => ; 
          case ExCaseClass(_,_,_) => ; 
          case ExConstructorDef() => ;
          case ExMainFunctionDef() => ;
          case ExFunctionDef(_,_,_,_) => ;
          case tree => { reporter.error(tree.pos, "Don't know what to do with this. Not purescala?"); println(tree) }
        }
      )

      val name: Identifier = FreshIdentifier(nameStr)
      val theDef = new ObjectDef(name, objectDefs.reverse ::: classDefs ::: funDefs, Nil)

      theDef
    }

    private def extractFunSig(nameStr: String, params: Seq[ValDef], tpt: Tree): FunDef = {
      val newParams = params.map(p => {
        val ptpe = toPureScalaType(p.tpt.tpe)
        val newID = FreshIdentifier(p.name.toString).setType(ptpe)
        owners += (Variable(newID) -> None)
        varSubsts(p.symbol) = (() => Variable(newID))
        VarDecl(newID, ptpe)
      })
      new FunDef(FreshIdentifier(nameStr), toPureScalaType(tpt.tpe), newParams)
    }

    private def extractFunDef(funDef: FunDef, body: Tree): FunDef = {
      currentFunDef = funDef

      val (body2, ensuring) = body match {
        case ExEnsuredExpression(body2, resSym, contract) =>
          varSubsts(resSym) = (() => ResultVariable().setType(funDef.returnType))
          (body2, toPureScala(contract))

        case ExHoldsExpression(body2) =>
          (body2, Some(ResultVariable().setType(BooleanType)))

        case _ =>
          (body, None)
      }

      val (body3, require) = body2 match {
        case ExRequiredExpression(body3, contract) =>
          (body3, toPureScala(contract))

        case _ =>
          (body2, None)
      }

      val finalBody = try {
        toPureScala(body3).map(flattenBlocks) match {
          case Some(e) if e.getType.isInstanceOf[ArrayType] =>
            getOwner(e) match {
              case Some(Some(fd)) if fd == funDef =>
                Some(e)

              case None =>
                Some(e)

              case _ =>
                reporter.error(body3.pos, "Function cannot return an array that is not locally defined")
                None
            }
          case e =>
            e
        }
      } catch {
        case e: ImpureCodeEncounteredException =>
        None
      }

      val finalRequire = require.filter{ e =>
        if(containsLetDef(e)) {
          reporter.error(body3.pos, "Function precondtion should not contain nested function definition")
          false
        } else {
          true
        }
      }

      val finalEnsuring = ensuring.filter{ e =>
        if(containsLetDef(e)) {
          reporter.error(body3.pos, "Function postcondition should not contain nested function definition")
          false
        } else {
          true
        }
      }

      funDef.body          = finalBody
      funDef.precondition  = finalRequire
      funDef.postcondition = finalEnsuring
      funDef
    }

    def extractProgram: Option[Program] = {
      val topLevelObjDef = extractTopLevelDef

      val programName: Identifier = unit.body match {
        case PackageDef(name, _) => FreshIdentifier(name.toString)
        case _                   => FreshIdentifier("<program>")
      }

      topLevelObjDef.map(obj => Program(programName, obj))
    }
  }

  private val mutableVarSubsts: scala.collection.mutable.Map[Symbol,Function0[Expr]] =
    scala.collection.mutable.Map.empty[Symbol,Function0[Expr]]
  private val varSubsts: scala.collection.mutable.Map[Symbol,Function0[Expr]] =
    scala.collection.mutable.Map.empty[Symbol,Function0[Expr]]
  private val classesToClasses: scala.collection.mutable.Map[Symbol,ClassTypeDef] =
    scala.collection.mutable.Map.empty[Symbol,ClassTypeDef]
  private val defsToDefs: scala.collection.mutable.Map[Symbol,FunDef] =
    scala.collection.mutable.Map.empty[Symbol,FunDef]


  /** An exception thrown when non-purescala compatible code is encountered. */
  sealed case class ImpureCodeEncounteredException(tree: Tree) extends Exception

  /** Attempts to convert a scalac AST to a pure scala AST. */


  private var currentFunDef: FunDef = null

  //This is a bit missleading, if an expr is not mapped then it has no owner, if it is mapped to None it means
  //that it can have any owner
  private var owners: Map[Expr, Option[FunDef]] = Map() 

  /** Forces conversion from scalac AST to purescala AST, throws an Exception
   * if impossible. */
  private def scala2PureScala(unit: CompilationUnit)(tree: Tree): Expr = {
    def rewriteCaseDef(cd: CaseDef): MatchCase = {

      def pat2pat(p: Tree, binder: Option[Identifier] = None): Pattern = p match {
        case b @ Bind(name, Typed(pat, tpe)) =>
          val newID = FreshIdentifier(name.toString).setType(scalaType2PureScala(unit)(tpe.tpe))
          varSubsts(b.symbol) = (() => Variable(newID))
          pat2pat(pat, Some(newID))

        case b @ Bind(name, pat) =>
          val newID = FreshIdentifier(name.toString).setType(scalaType2PureScala(unit)(b.symbol.tpe))
          varSubsts(b.symbol) = (() => Variable(newID))
          pat2pat(pat, Some(newID))

        case Ident(nme.WILDCARD) =>
          WildcardPattern(binder)

        case s @ Select(This(_), b) if s.tpe.typeSymbol.isCase &&
                                       classesToClasses.keySet.contains(s.tpe.typeSymbol) =>
          // case Obj =>
          val cd = classesToClasses(s.tpe.typeSymbol).asInstanceOf[CaseClassDef]
          assert(cd.fields.size == 0)
          CaseClassPattern(binder, cd, Seq())

        case a @ Apply(fn, args) if fn.isType &&
                                    a.tpe.typeSymbol.isCase &&
                                    classesToClasses.keySet.contains(a.tpe.typeSymbol) =>

          val cd = classesToClasses(a.tpe.typeSymbol).asInstanceOf[CaseClassDef]
          assert(args.size == cd.fields.size)
          CaseClassPattern(binder, cd, args.map(pat2pat(_)))

        case a @ Apply(fn, args) =>
          val pst = scalaType2PureScala(unit)(a.tpe)
          pst match {
            case TupleType(argsTpes) => TuplePattern(binder, args.map(pat2pat(_)))
            case _ => throw ImpureCodeEncounteredException(p)
          }

        case _ =>
          reporter.error(p.pos, "Unsupported pattern.")
          throw ImpureCodeEncounteredException(p)
      }

      if(cd.guard == EmptyTree) {
        SimpleCase(pat2pat(cd.pat), rec(cd.body))
      } else {
        val recPattern = pat2pat(cd.pat)
        val recGuard = rec(cd.guard)
        val recBody = rec(cd.body)
        if(!isPure(recGuard)) {
          reporter.error(cd.guard.pos, "Guard expression must be pure")
          throw ImpureCodeEncounteredException(cd)
        }
        GuardedCase(recPattern, recGuard, recBody)
      }
    }

    def extractFunSig(nameStr: String, params: Seq[ValDef], tpt: Tree): FunDef = {
      val newParams = params.map(p => {
        val ptpe =  scalaType2PureScala(unit) (p.tpt.tpe)
        val newID = FreshIdentifier(p.name.toString).setType(ptpe)
        owners += (Variable(newID) -> None)
        varSubsts(p.symbol) = (() => Variable(newID))
        VarDecl(newID, ptpe)
      })
      new FunDef(FreshIdentifier(nameStr), scalaType2PureScala(unit)(tpt.tpe), newParams)
    }

    def extractFunDef2(funDef: FunDef, body: Tree): FunDef = {
      currentFunDef = funDef

      val (body2, ensuring) = body match {
        case ExEnsuredExpression(body2, resSym, contract) =>
          varSubsts(resSym) = (() => ResultVariable().setType(funDef.returnType))

          (body2, Some(scala2PureScala(unit)(contract)))

        case ExHoldsExpression(body2) =>
          (body2, Some(ResultVariable().setType(BooleanType)))

        case _ =>
          (body, None)
      }

      val (body3, require) = body2 match {
        case ExRequiredExpression(body3, contract) =>
          (body3, Some(scala2PureScala(unit) (contract)))

        case _ =>
          (body2, None)
      }

      val finalBody = try {
        val e = flattenBlocks(scala2PureScala(unit)(body3))

        if (e.getType.isInstanceOf[ArrayType]) {
          getOwner(e) match {
            case Some(Some(fd)) if fd == funDef =>
              Some(e)

            case None =>
              Some(e)

            case _ =>
              reporter.error(body3.pos, "Function cannot return an array that is not locally defined")
              None
          }
        } else {
          Some(e)
        }

      } catch {
        case e: ImpureCodeEncounteredException =>
          None
      }

      val finalRequire = require.filter{ e =>
        if (containsLetDef(e)) {
          reporter.error(body3.pos, "Function precondtion should not contain nested function definition")
          false
        } else {
          true
        }
      }

      val finalEnsuring = ensuring.filter{ e =>
        if (containsLetDef(e)) {
          reporter.error(body3.pos, "Function postconfition should not contain nested function definition")
          false
        } else {
          true
        }
      }

      funDef.body          = finalBody
      funDef.precondition  = finalRequire
      funDef.postcondition = finalEnsuring

      funDef
    }

    def rec(tr: Tree): Expr = {
      val (nextExpr, rest) = tr match {
        case Block(Block(e :: es1, l1) :: es2, l2) => (e, Some(Block(es1 ++ Seq(l1) ++ es2, l2)))
        case Block(e :: Nil, last) => (e, Some(last))
        case Block(e :: es, last) => (e, Some(Block(es, last)))
        case _ => (tr, None)
      }

      val e2: Option[Expr] = nextExpr match {
        case ExCaseObject(sym) =>
          classesToClasses.get(sym) match {
            case Some(ccd: CaseClassDef) =>
              Some(CaseClass(ccd, Seq()))
            case _ =>
              None
          }

        case ExParameterlessMethodCall(t,n) => {
          val selector = rec(t)
          val selType = selector.getType

          if(!selType.isInstanceOf[CaseClassType])
            None
          else {

            val selDef: CaseClassDef = selType.asInstanceOf[CaseClassType].classDef

            val fieldID = selDef.fields.find(_.id.name == n.toString) match {
              case None =>
                reporter.error(tr.pos, "Invalid method or field invocation (not a case class arg?)")
                throw ImpureCodeEncounteredException(tr)

              case Some(vd) =>
                vd.id
            }

            Some(CaseClassSelector(selDef, selector, fieldID).setType(fieldID.getType))
          }
        }
        case _ => None
      }
      var handleRest = true
      val psExpr = e2 match {
        case Some(e3) => e3
        case None => nextExpr match {
          case ExTuple(tpes, exprs) => {
            val tupleExprs = exprs.map(e => rec(e))
            val tupleType = TupleType(tupleExprs.map(expr => expr.getType))
            Tuple(tupleExprs).setType(tupleType)
          }
          case ExErrorExpression(str, tpe) =>
            Error(str).setType(scalaType2PureScala(unit)(tpe))

          case ExTupleExtract(tuple, index) => {
            val tupleExpr = rec(tuple)
            val TupleType(tpes) = tupleExpr.getType
            if(tpes.size < index)
              throw ImpureCodeEncounteredException(tree)
            else
              TupleSelect(tupleExpr, index).setType(tpes(index-1))
          }
          case ExValDef(vs, tpt, bdy) => {
            val binderTpe = scalaType2PureScala(unit)(tpt.tpe)
            val newID = FreshIdentifier(vs.name.toString).setType(binderTpe)
            val valTree = rec(bdy)
            handleRest = false
            if(valTree.getType.isInstanceOf[ArrayType]) {
              getOwner(valTree) match {
                case None =>
                  owners += (Variable(newID) -> Some(currentFunDef))
                case Some(_) =>
                  reporter.error(nextExpr.pos, "Cannot alias array")
                  throw ImpureCodeEncounteredException(nextExpr)
              }
            }
            val restTree = rest match {
              case Some(rst) => {
                varSubsts(vs) = (() => Variable(newID))
                val res = rec(rst)
                varSubsts.remove(vs)
                res
              }
              case None => UnitLiteral
            }
            val res = Let(newID, valTree, restTree)
            res
          }
          case dd@ExFunctionDef(n, p, t, b) => {
            val funDef = extractFunSig(n, p, t).setPosInfo(dd.pos.line, dd.pos.column)
            defsToDefs += (dd.symbol -> funDef)
            val oldMutableVarSubst = mutableVarSubsts.toMap //take an immutable snapshot of the map
            val oldCurrentFunDef = currentFunDef
            mutableVarSubsts.clear //reseting the visible mutable vars, we do not handle mutable variable closure in nested functions
            val funDefWithBody = extractFunDef2(funDef, b)
            mutableVarSubsts ++= oldMutableVarSubst
            currentFunDef = oldCurrentFunDef
            val restTree = rest match {
              case Some(rst) => rec(rst)
              case None => UnitLiteral
            }
            defsToDefs.remove(dd.symbol)
            handleRest = false
            LetDef(funDefWithBody, restTree)
          }
          case ExVarDef(vs, tpt, bdy) => {
            val binderTpe = scalaType2PureScala(unit)(tpt.tpe)
            //binderTpe match {
            //  case ArrayType(_) => 
            //    reporter.error(tree.pos, "Cannot declare array variables, only val are alllowed")
            //    throw ImpureCodeEncounteredException(tree)
            //  case _ =>
            //}
            val newID = FreshIdentifier(vs.name.toString).setType(binderTpe)
            val valTree = rec(bdy)
            mutableVarSubsts += (vs -> (() => Variable(newID)))
            handleRest = false
            if(valTree.getType.isInstanceOf[ArrayType]) {
              getOwner(valTree) match {
                case None =>
                  owners += (Variable(newID) -> Some(currentFunDef))
                case Some(_) =>
                  reporter.error(nextExpr.pos, "Cannot alias array")
                  throw ImpureCodeEncounteredException(nextExpr)
              }
            }
            val restTree = rest match {
              case Some(rst) => {
                varSubsts(vs) = (() => Variable(newID))
                val res = rec(rst)
                varSubsts.remove(vs)
                res
              }
              case None => UnitLiteral
            }
            val res = LetVar(newID, valTree, restTree)
            res
          }

          case ExAssign(sym, rhs) => mutableVarSubsts.get(sym) match {
            case Some(fun) => {
              val Variable(id) = fun()
              val rhsTree = rec(rhs)
              if(rhsTree.getType.isInstanceOf[ArrayType]) {
                getOwner(rhsTree) match {
                  case None =>
                  case Some(_) =>
                    unit.error(nextExpr.pos, "Cannot alias array")
                    throw ImpureCodeEncounteredException(nextExpr)
                }
              }
              Assignment(id, rhsTree)
            }
            case None => {
              unit.error(tr.pos, "Undeclared variable.")
              throw ImpureCodeEncounteredException(tr)
            }
          }
          case wh@ExWhile(cond, body) => {
            val condTree = rec(cond)
            val bodyTree = rec(body)
            While(condTree, bodyTree).setPosInfo(wh.pos.line,wh.pos.column)
          }
          case wh@ExWhileWithInvariant(cond, body, inv) => {
            val condTree = rec(cond)
            val bodyTree = rec(body)
            val invTree = rec(inv)
            val w = While(condTree, bodyTree).setPosInfo(wh.pos.line,wh.pos.column)
            w.invariant = Some(invTree)
            w
          }

          case ExInt32Literal(v) => IntLiteral(v).setType(Int32Type)
          case ExBooleanLiteral(v) => BooleanLiteral(v).setType(BooleanType)
          case ExUnitLiteral() => UnitLiteral
          case ExLocally(body) => rec(body)
          case ExTyped(e,tpt) => rec(e)
          case ExIdentifier(sym,tpt) => varSubsts.get(sym) match {
            case Some(fun) => fun()
            case None => mutableVarSubsts.get(sym) match {
              case Some(fun) => fun()
              case None => {
                unit.error(tr.pos, "Unidentified variable.")
                throw ImpureCodeEncounteredException(tr)
              }
            }
          }
          case epsi@ExEpsilonExpression(tpe, varSym, predBody) => {
            val pstpe = scalaType2PureScala(unit)(tpe)
            val previousVarSubst: Option[Function0[Expr]] = varSubsts.get(varSym) //save the previous in case of nested epsilon
            varSubsts(varSym) = (() => EpsilonVariable((epsi.pos.line, epsi.pos.column)).setType(pstpe))
            val c1 = rec(predBody)
            previousVarSubst match {
              case Some(f) => varSubsts(varSym) = f
              case None => varSubsts.remove(varSym)
            }
            if(containsEpsilon(c1)) {
              unit.error(epsi.pos, "Usage of nested epsilon is not allowed.")
              throw ImpureCodeEncounteredException(epsi)
            }
            Epsilon(c1).setType(pstpe).setPosInfo(epsi.pos.line, epsi.pos.column)
          }

          case chs @ ExChooseExpression(args, tpe, body, select) => {
            val cTpe  = scalaType2PureScala(unit)(tpe)

            val vars = args map { case (tpe, sym) =>
              val aTpe  = scalaType2PureScala(unit)(tpe)
              val newID = FreshIdentifier(sym.name.toString).setType(aTpe)
              owners += (Variable(newID) -> None)
              varSubsts(sym) = (() => Variable(newID))
              newID
            }

            val cBody = rec(body)

            Choose(vars, cBody).setType(cTpe).setPosInfo(select.pos.line, select.pos.column)
          }

          case ExWaypointExpression(tpe, i, tree) => {
            val pstpe = scalaType2PureScala(unit)(tpe)
            val IntLiteral(ri) = rec(i)
            Waypoint(ri, rec(tree)).setType(pstpe)
          }
          case ExCaseClassConstruction(tpt, args) => {
            val cctype = scalaType2PureScala(unit)(tpt.tpe)
            if(!cctype.isInstanceOf[CaseClassType]) {
              unit.error(tr.pos, "Construction of a non-case class.")
              throw ImpureCodeEncounteredException(tree)
            }
            val nargs = args.map(rec(_))
            val cct = cctype.asInstanceOf[CaseClassType]
            CaseClass(cct.classDef, nargs).setType(cct)
          }

          case ExAnd(l, r) => And(rec(l), rec(r)).setType(BooleanType)
          case ExOr(l, r) => Or(rec(l), rec(r)).setType(BooleanType)
          case ExNot(e) => Not(rec(e)).setType(BooleanType)
          case ExUMinus(e) => UMinus(rec(e)).setType(Int32Type)
          case ExPlus(l, r) => Plus(rec(l), rec(r)).setType(Int32Type)
          case ExMinus(l, r) => Minus(rec(l), rec(r)).setType(Int32Type)
          case ExTimes(l, r) => Times(rec(l), rec(r)).setType(Int32Type)
          case ExDiv(l, r) => Division(rec(l), rec(r)).setType(Int32Type)
          case ExMod(l, r) => Modulo(rec(l), rec(r)).setType(Int32Type)
          case ExEquals(l, r) => {
            val rl = rec(l)
            val rr = rec(r)
            ((rl.getType,rr.getType) match {
              case (SetType(_), SetType(_)) => SetEquals(rl, rr)
              case (BooleanType, BooleanType) => Iff(rl, rr)
              case (_, _) => Equals(rl, rr)
            }).setType(BooleanType) 
          }
          case ExNotEquals(l, r) => Not(Equals(rec(l), rec(r)).setType(BooleanType)).setType(BooleanType)
          case ExGreaterThan(l, r) => GreaterThan(rec(l), rec(r)).setType(BooleanType)
          case ExGreaterEqThan(l, r) => GreaterEquals(rec(l), rec(r)).setType(BooleanType)
          case ExLessThan(l, r) => LessThan(rec(l), rec(r)).setType(BooleanType)
          case ExLessEqThan(l, r) => LessEquals(rec(l), rec(r)).setType(BooleanType)
          case ExFiniteSet(tt, args) => {
            val underlying = scalaType2PureScala(unit)(tt.tpe)
            FiniteSet(args.map(rec(_))).setType(SetType(underlying))
          }
          case ExFiniteMultiset(tt, args) => {
            val underlying = scalaType2PureScala(unit)(tt.tpe)
            FiniteMultiset(args.map(rec(_))).setType(MultisetType(underlying))
          }
          case ExEmptySet(tt) => {
            val underlying = scalaType2PureScala(unit)(tt.tpe)
            FiniteSet(Seq()).setType(SetType(underlying))
          }
          case ExEmptyMultiset(tt) => {
            val underlying = scalaType2PureScala(unit)(tt.tpe)
            EmptyMultiset(underlying).setType(MultisetType(underlying))
          }
          case ExEmptyMap(ft, tt) => {
            val fromUnderlying = scalaType2PureScala(unit)(ft.tpe)
            val toUnderlying   = scalaType2PureScala(unit)(tt.tpe)
            val tpe = MapType(fromUnderlying, toUnderlying)

            FiniteMap(Seq()).setType(tpe)
          }
          case ExLiteralMap(ft, tt, elems) => {
            val fromUnderlying = scalaType2PureScala(unit)(ft.tpe)
            val toUnderlying   = scalaType2PureScala(unit)(tt.tpe)
            val tpe = MapType(fromUnderlying, toUnderlying)

            val singletons: Seq[(Expr, Expr)] = elems.collect { case ExTuple(tpes, trees) if (trees.size == 2) =>
              (rec(trees(0)), rec(trees(1)))
            }

            if (singletons.size != elems.size) {
              unit.error(nextExpr.pos, "Some map elements could not be extracted as Tuple2")
              throw ImpureCodeEncounteredException(nextExpr)
            }

            FiniteMap(singletons).setType(tpe)
          }

          case ExSetMin(t) => {
            val set = rec(t)
            if(!set.getType.isInstanceOf[SetType]) {
              unit.error(t.pos, "Min should be computed on a set.")
              throw ImpureCodeEncounteredException(tree)
            }
            SetMin(set).setType(set.getType.asInstanceOf[SetType].base)
          }
          case ExSetMax(t) => {
            val set = rec(t)
            if(!set.getType.isInstanceOf[SetType]) {
              unit.error(t.pos, "Max should be computed on a set.")
              throw ImpureCodeEncounteredException(tree)
            }
            SetMax(set).setType(set.getType.asInstanceOf[SetType].base)
          }
          case ExUnion(t1,t2) => {
            val rl = rec(t1)
            val rr = rec(t2)
            rl.getType match {
              case s @ SetType(_) => SetUnion(rl, rr).setType(s)
              case m @ MultisetType(_) => MultisetUnion(rl, rr).setType(m)
              case _ => {
                unit.error(tree.pos, "Union of non set/multiset expressions.")
                throw ImpureCodeEncounteredException(tree)
              }
            }
          }
          case ExIntersection(t1,t2) => {
            val rl = rec(t1)
            val rr = rec(t2)
            rl.getType match {
              case s @ SetType(_) => SetIntersection(rl, rr).setType(s)
              case m @ MultisetType(_) => MultisetIntersection(rl, rr).setType(m)
              case _ => {
                unit.error(tree.pos, "Intersection of non set/multiset expressions.")
                throw ImpureCodeEncounteredException(tree)
              }
            }
          }
          case ExSetContains(t1,t2) => {
            val rl = rec(t1)
            val rr = rec(t2)
            rl.getType match {
              case s @ SetType(_) => ElementOfSet(rr, rl)
              case _ => {
                unit.error(tree.pos, ".contains on non set expression.")
                throw ImpureCodeEncounteredException(tree)
              }
            }
          }
          case ExSetSubset(t1,t2) => {
            val rl = rec(t1)
            val rr = rec(t2)
            rl.getType match {
              case s @ SetType(_) => SubsetOf(rl, rr)
              case _ => {
                unit.error(tree.pos, "Subset on non set expression.")
                throw ImpureCodeEncounteredException(tree)
              }
            }
          }
          case ExSetMinus(t1,t2) => {
            val rl = rec(t1)
            val rr = rec(t2)
            rl.getType match {
              case s @ SetType(_) => SetDifference(rl, rr).setType(s)
              case m @ MultisetType(_) => MultisetDifference(rl, rr).setType(m)
              case _ => {
                unit.error(tree.pos, "Difference of non set/multiset expressions.")
                throw ImpureCodeEncounteredException(tree)
              }
            }
          } 
          case ExSetCard(t) => {
            val rt = rec(t)
            rt.getType match {
              case s @ SetType(_) => SetCardinality(rt)
              case m @ MultisetType(_) => MultisetCardinality(rt)
              case _ => {
                unit.error(tree.pos, "Cardinality of non set/multiset expressions.")
                throw ImpureCodeEncounteredException(tree)
              }
            }
          }
          case ExMultisetToSet(t) => {
            val rt = rec(t)
            rt.getType match {
              case m @ MultisetType(u) => MultisetToSet(rt).setType(SetType(u))
              case _ => {
                unit.error(tree.pos, "toSet can only be applied to multisets.")
                throw ImpureCodeEncounteredException(tree)
              }
            }
          }
          case up@ExUpdated(m,f,t) => {
            val rm = rec(m)
            val rf = rec(f)
            val rt = rec(t)
            rm.getType match {
              case MapType(ft, tt) => {
                MapUnion(rm, FiniteMap(Seq((rf, rt))).setType(rm.getType)).setType(rm.getType)
              }
              case ArrayType(bt) => {
                ArrayUpdated(rm, rf, rt).setType(rm.getType).setPosInfo(up.pos.line, up.pos.column)
              }
              case _ => {
                unit.error(tree.pos, "updated can only be applied to maps.")
                throw ImpureCodeEncounteredException(tree)
              }
            }
          }
          case ExMapIsDefinedAt(m,k) => {
            val rm = rec(m)
            val rk = rec(k)
            MapIsDefinedAt(rm, rk)
          }

          case ExPlusPlusPlus(t1,t2) => {
            val rl = rec(t1)
            val rr = rec(t2)
            MultisetPlus(rl, rr).setType(rl.getType)
          }
          case app@ExApply(lhs,args) => {
            val rlhs = rec(lhs)
            val rargs = args map rec
            rlhs.getType match {
              case MapType(_,tt) => 
                assert(rargs.size == 1)
                MapGet(rlhs, rargs.head).setType(tt).setPosInfo(app.pos.line, app.pos.column)
              case ArrayType(bt) => {
                assert(rargs.size == 1)
                ArraySelect(rlhs, rargs.head).setType(bt).setPosInfo(app.pos.line, app.pos.column)
              }
              case _ => {
                unit.error(tree.pos, "apply on unexpected type")
                throw ImpureCodeEncounteredException(tree)
              }
            }
          }
          // for now update only occurs on Array. later we might have to distinguished depending on the type of the lhs
          case update@ExUpdate(lhs, index, newValue) => { 
            val lhsRec = rec(lhs)
            lhsRec match {
              case Variable(_) =>
              case _ => {
                unit.error(tree.pos, "array update only works on variables")
                throw ImpureCodeEncounteredException(tree)
              }
            }
            getOwner(lhsRec) match {
              case Some(Some(fd)) if fd != currentFunDef => 
                unit.error(nextExpr.pos, "cannot update an array that is not defined locally")
                throw ImpureCodeEncounteredException(nextExpr)
              case Some(None) =>
                unit.error(nextExpr.pos, "cannot update an array that is not defined locally")
                throw ImpureCodeEncounteredException(nextExpr)
              case Some(_) =>
              case None => sys.error("This array: " + lhsRec + " should have had an owner")
            }
            val indexRec = rec(index)
            val newValueRec = rec(newValue)
            ArrayUpdate(lhsRec, indexRec, newValueRec).setPosInfo(update.pos.line, update.pos.column)
          }
          case ExArrayLength(t) => {
            val rt = rec(t)
            ArrayLength(rt)
          }
          case ExArrayClone(t) => {
            val rt = rec(t)
            ArrayClone(rt)
          }
          case ExArrayFill(baseType, length, defaultValue) => {
            val underlying = scalaType2PureScala(unit)(baseType.tpe)
            val lengthRec = rec(length)
            val defaultValueRec = rec(defaultValue)
            ArrayFill(lengthRec, defaultValueRec).setType(ArrayType(underlying))
          }
          case ExIfThenElse(t1,t2,t3) => {
            val r1 = rec(t1)
            if(containsLetDef(r1)) {
              unit.error(t1.pos, "Condition of if-then-else expression should not contain nested function definition")
              throw ImpureCodeEncounteredException(t1)
            }
            val r2 = rec(t2)
            val r3 = rec(t3)
            val lub = leastUpperBound(r2.getType, r3.getType)
            lub match {
              case Some(lub) => IfExpr(r1, r2, r3).setType(lub)
              case None =>
                unit.error(nextExpr.pos, "Both branches of ifthenelse have incompatible types")
                throw ImpureCodeEncounteredException(t1)
            }
          }

          case ExIsInstanceOf(tt, cc) => {
            val ccRec = rec(cc)
            val checkType = scalaType2PureScala(unit)(tt.tpe)
            checkType match {
              case CaseClassType(ccd) => {
                val rootType: ClassTypeDef  = if(ccd.parent != None) ccd.parent.get else ccd
                if(!ccRec.getType.isInstanceOf[ClassType]) {
                  unit.error(tr.pos, "isInstanceOf can only be used with a case class")
                  throw ImpureCodeEncounteredException(tr)
                } else {
                  val testedExprType = ccRec.getType.asInstanceOf[ClassType].classDef
                  val testedExprRootType: ClassTypeDef = if(testedExprType.parent != None) testedExprType.parent.get else testedExprType

                  if(rootType != testedExprRootType) {
                    unit.error(tr.pos, "isInstanceOf can only be used with compatible case classes")
                    throw ImpureCodeEncounteredException(tr)
                  } else {
                    CaseClassInstanceOf(ccd, ccRec) 
                  }
                }
              }
              case _ => {
                unit.error(tr.pos, "isInstanceOf can only be used with a case class")
                throw ImpureCodeEncounteredException(tr)
              }
            }
          }

          case lc @ ExLocalCall(sy,nm,ar) => {
            if(defsToDefs.keysIterator.find(_ == sy).isEmpty) {
              unit.error(tr.pos, "Invoking an invalid function.")
              throw ImpureCodeEncounteredException(tr)
            }
            val fd = defsToDefs(sy)
            FunctionInvocation(fd, ar.map(rec(_))).setType(fd.returnType).setPosInfo(lc.pos.line,lc.pos.column) 
          }

          case pm @ ExPatternMatching(sel, cses) => {
            val rs = rec(sel)
            val rc = cses.map(rewriteCaseDef(_))
            val rt: purescala.TypeTrees.TypeTree = rc.map(_.rhs.getType).reduceLeft(leastUpperBound(_,_).get)
            MatchExpr(rs, rc).setType(rt).setPosInfo(pm.pos.line,pm.pos.column)
          }

      
          // default behaviour is to complain :)
          case _ => {
            reporter.info(tr.pos, "Could not extract as PureScala.", true)
            throw ImpureCodeEncounteredException(tree)
          }
        }
      }

      val res = if(handleRest) {
        rest match {
          case Some(rst) => {
            val recRst = rec(rst)
            val block = PBlock(Seq(psExpr), recRst).setType(recRst.getType)
            block
          }
          case None => psExpr
        }
      } else {
        psExpr
      }

      res
    }
    rec(tree)
  }

  private def scalaType2PureScala(unit: CompilationUnit)(tree: Type): purescala.TypeTrees.TypeTree = {

    def rec(tr: Type): purescala.TypeTrees.TypeTree = tr match {
      case tpe if tpe == IntClass.tpe => Int32Type
      case tpe if tpe == BooleanClass.tpe => BooleanType
      case tpe if tpe == UnitClass.tpe => UnitType
      case tpe if tpe == NothingClass.tpe => BottomType
      case TypeRef(_, sym, btt :: Nil) if isSetTraitSym(sym) => SetType(rec(btt))
      case TypeRef(_, sym, btt :: Nil) if isMultisetTraitSym(sym) => MultisetType(rec(btt))
      case TypeRef(_, sym, List(ftt,ttt)) if isMapTraitSym(sym) => MapType(rec(ftt),rec(ttt))
      case TypeRef(_, sym, List(t1,t2)) if isTuple2(sym) => TupleType(Seq(rec(t1),rec(t2)))
      case TypeRef(_, sym, List(t1,t2,t3)) if isTuple3(sym) => TupleType(Seq(rec(t1),rec(t2),rec(t3)))
      case TypeRef(_, sym, List(t1,t2,t3,t4)) if isTuple4(sym) => TupleType(Seq(rec(t1),rec(t2),rec(t3),rec(t4)))
      case TypeRef(_, sym, List(t1,t2,t3,t4,t5)) if isTuple5(sym) => TupleType(Seq(rec(t1),rec(t2),rec(t3),rec(t4),rec(t5)))
      case TypeRef(_, sym, btt :: Nil) if isArrayClassSym(sym) => ArrayType(rec(btt))
      case TypeRef(_, sym, Nil) if classesToClasses.keySet.contains(sym) => classDefToClassType(classesToClasses(sym))
      case _ => {
        unit.error(NoPosition, "Could not extract type as PureScala. [" + tr + "]")
        throw ImpureCodeEncounteredException(null)
      }
    }

    rec(tree)
  }

  def mkPosString(pos: scala.tools.nsc.util.Position) : String = {
    pos.line + "," + pos.column
  }

  def getReturnedExpr(expr: Expr): Seq[Expr] = expr match {
    case Let(_, _, rest) => getReturnedExpr(rest)
    case LetVar(_, _, rest) => getReturnedExpr(rest)
    case PBlock(_, rest) => getReturnedExpr(rest)
    case IfExpr(_, then, elze) => getReturnedExpr(then) ++ getReturnedExpr(elze)
    case MatchExpr(_, cses) => cses.flatMap{
      case SimpleCase(_, rhs) => getReturnedExpr(rhs)
      case GuardedCase(_, _, rhs) => getReturnedExpr(rhs)
    }
    case _ => Seq(expr)
  }

  def getOwner(exprs: Seq[Expr]): Option[Option[FunDef]] = {
    val exprOwners: Seq[Option[Option[FunDef]]] = exprs.map(owners.get(_))
    if(exprOwners.exists(_ == None))
      None
    else if(exprOwners.exists(_ == Some(None)))
      Some(None)
    else if(exprOwners.exists(o1 => exprOwners.exists(o2 => o1 != o2)))
      Some(None)
    else
      exprOwners(0)
  }

  def getOwner(expr: Expr): Option[Option[FunDef]] = getOwner(getReturnedExpr(expr))

}
