/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package plugin

import scala.tools.nsc._
import scala.tools.nsc.plugins._

import purescala.Definitions._
import purescala.Trees._
import xlang.Trees.{Block => LeonBlock, _}
import xlang.TreeOps._
import purescala.TypeTrees.{TypeTree => LeonType, _}
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

  class ScalaPos(p: global.Position) extends ScalacPositional {
    setPosInfo(p.line, p.column)
  }

  implicit def scalaPosToLeonPos(p: global.Position): ScalacPositional = {
    new ScalaPos(p)
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


  class Extraction(unit: CompilationUnit) {
    def toPureScala(tree: Tree): Option[Expr] = {
      try {
        Some(extractTree(tree))
      } catch {
        case e: ImpureCodeEncounteredException =>
          None
      }
    }

    // This one never fails, on error, it returns Untyped
    def toPureScalaType(tpt: Type): LeonType = {
      try {
        extractType(tpt)
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

      var scalaClassSyms  = Map[Symbol,Identifier]()
      var scalaClassArgs  = Map[Symbol,Seq[(String,Tree)]]()
      var scalaClassNames = Set[String]()

      // we need the new type definitions before we can do anything...
      for (t <- tmpl.body) t match {
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

      }

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

      // First pass to instanciate all FunDefs
      for (d <- tmpl.body) d match {
        case ExMainFunctionDef() =>
          // we ignore the main function

        case dd @ ExFunctionDef(name, params, tpe, body) =>
          val funDef = extractFunSig(name, params, tpe).setPosInfo(dd.pos)

          if (dd.mods.isPrivate) {
            funDef.addAnnotation("private")
          }

          for(a <- dd.symbol.annotations) {
            a.atp.safeToString match {
              case "leon.Annotations.induct"     => funDef.addAnnotation("induct")
              case "leon.Annotations.axiomatize" => funDef.addAnnotation("axiomatize")
              case "leon.Annotations.main"       => funDef.addAnnotation("main")
              case _ => ;
            }
          }

          defsToDefs += dd.symbol -> funDef

        case _ =>
      }

      // Second pass to convert function bodies
      for (d <- tmpl.body) d match {
        case dd @ ExFunctionDef(_, _, _, body) if defsToDefs contains dd.symbol =>
          val fd = defsToDefs(dd.symbol)

          extractFunDef(fd, body)
        case _ =>
      }

      var funDefs: List[FunDef] = defsToDefs.values.toList

      // FIXME: we check nothing else is polluting the object
      for (t <- tmpl.body) t match {
        case ExCaseClassSyntheticJunk() =>
        case ExAbstractClass(_,_) =>
        case ExCaseClass(_,_,_) =>
        case ExConstructorDef() =>
        case ExMainFunctionDef() =>
        case ExFunctionDef(_,_,_,_) =>
        case tree =>
          reporter.error(tree.pos, "Don't know what to do with this. Not purescala?");
          println(tree)
      }

      new ObjectDef(FreshIdentifier(nameStr), classDefs ::: funDefs, Nil)
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

    def unsupported(msg: String): Nothing = {
      reporter.error(NoPosition, msg)
      throw new ImpureCodeEncounteredException(null)
    }
    def unsupported(tr: Tree, msg: String): Nothing = {
      reporter.error(tr.pos, msg)
      throw new ImpureCodeEncounteredException(tr)
    }


    private def extractPattern(p: Tree, binder: Option[Identifier] = None): Pattern = p match {
      case b @ Bind(name, Typed(pat, tpe)) =>
        val newID = FreshIdentifier(name.toString).setType(extractType(tpe.tpe))
        varSubsts(b.symbol) = (() => Variable(newID))
        extractPattern(pat, Some(newID))

      case b @ Bind(name, pat) =>
        val newID = FreshIdentifier(name.toString).setType(extractType(b.symbol.tpe))
        varSubsts(b.symbol) = (() => Variable(newID))
        extractPattern(pat, Some(newID))

      case Ident(nme.WILDCARD) =>
        WildcardPattern(binder)

      case s @ Select(This(_), b) if s.tpe.typeSymbol.isCase &&
                                     classesToClasses.contains(s.tpe.typeSymbol) =>
        // case Obj =>
        val cd = classesToClasses(s.tpe.typeSymbol).asInstanceOf[CaseClassDef]
        assert(cd.fields.size == 0)
        CaseClassPattern(binder, cd, Seq())

      case a @ Apply(fn, args) if fn.isType &&
                                  a.tpe.typeSymbol.isCase &&
                                  classesToClasses.contains(a.tpe.typeSymbol) =>

        val cd = classesToClasses(a.tpe.typeSymbol).asInstanceOf[CaseClassDef]
        assert(args.size == cd.fields.size)
        CaseClassPattern(binder, cd, args.map(extractPattern(_)))

      case a @ Apply(fn, args) =>
        extractType(a.tpe) match {
          case TupleType(argsTpes) =>
            TuplePattern(binder, args.map(extractPattern(_)))
          case _ =>
            unsupported(p, "Unsupported pattern")
        }

      case _ =>
        unsupported(p, "Unsupported pattern")
    }

    private def extractMatchCase(cd: CaseDef): MatchCase = {
      val recPattern = extractPattern(cd.pat)
      val recBody    = extractTree(cd.body)

      if(cd.guard == EmptyTree) {
        SimpleCase(recPattern, recBody)
      } else {
        val recGuard = extractTree(cd.guard)

        if(!isPure(recGuard)) {
          reporter.error(cd.guard.pos, "Guard expression must be pure")
          throw ImpureCodeEncounteredException(cd)
        }

        GuardedCase(recPattern, recGuard, recBody)
      }
    }

    private def extractTree(tr: Tree): Expr = {
      val (current, tmpRest) = tr match {
        case Block(e :: Nil, last) =>
          (e, Some(last))
        case Block(e :: es, last) =>
          (e, Some(Block(es, last)))
        case e =>
          (e, None)
      }

      var rest = tmpRest

      val res = current match {
        case ExCaseObject(sym) =>
          classesToClasses.get(sym) match {
            case Some(ccd: CaseClassDef) =>
              CaseClass(ccd, Seq())

            case _ =>
              unsupported(tr, "Unknown case class "+sym.name)
          }

        case ExParameterlessMethodCall(t,n) =>
          val selector = extractTree(t)
          val selType = selector.getType

          if(!selType.isInstanceOf[CaseClassType]) {
            unsupported(tr, "Calling a method on a non-case-class?")
          } else {
            val selDef: CaseClassDef = selType.asInstanceOf[CaseClassType].classDef

            val fieldID = selDef.fields.find(_.id.name == n.toString) match {
              case None =>
                unsupported(tr, "Invalid method or field invocation (not a case class arg?)")

              case Some(vd) =>
                vd.id
            }

            CaseClassSelector(selDef, selector, fieldID).setType(fieldID.getType)
          }

        case ExTuple(tpes, exprs) =>
          val tupleExprs = exprs.map(e => extractTree(e))
          val tupleType = TupleType(tupleExprs.map(expr => expr.getType))
          Tuple(tupleExprs).setType(tupleType)

        case ExErrorExpression(str, tpe) =>
          Error(str).setType(extractType(tpe))

        case ExTupleExtract(tuple, index) =>
          val tupleExpr = extractTree(tuple)

          tupleExpr.getType match {
            case TupleType(tpes) if tpes.size >= index =>
              TupleSelect(tupleExpr, index).setType(tpes(index-1))

            case _ =>
              unsupported(tr, "Invalid tupple access")
          }

        case ExValDef(vs, tpt, bdy) =>
          val binderTpe = extractType(tpt.tpe)
          val newID = FreshIdentifier(vs.name.toString).setType(binderTpe)
          val valTree = extractTree(bdy)

          if(valTree.getType.isInstanceOf[ArrayType]) {
            getOwner(valTree) match {
              case None =>
                owners += (Variable(newID) -> Some(currentFunDef))
              case Some(_) =>
                reporter.error(tr.pos, "Cannot alias array")
                throw ImpureCodeEncounteredException(tr)
            }
          }
          val restTree = rest match {
            case Some(rst) => {
              varSubsts(vs) = (() => Variable(newID))
              val res = extractTree(rst)
              varSubsts.remove(vs)
              res
            }
            case None => UnitLiteral
          }

          rest = None
          Let(newID, valTree, restTree)

        case dd@ExFunctionDef(n, p, t, b) =>
          val funDef = extractFunSig(n, p, t).setPosInfo(dd.pos.line, dd.pos.column)
          defsToDefs += (dd.symbol -> funDef)
          val oldMutableVarSubst = mutableVarSubsts.toMap //take an immutable snapshot of the map
          val oldCurrentFunDef = currentFunDef
          mutableVarSubsts.clear //reseting the visible mutable vars, we do not handle mutable variable closure in nested functions
          val funDefWithBody = extractFunDef(funDef, b)
          mutableVarSubsts ++= oldMutableVarSubst
          currentFunDef = oldCurrentFunDef
          val restTree = rest match {
            case Some(rst) => extractTree(rst)
            case None => UnitLiteral
          }
          defsToDefs.remove(dd.symbol)
          rest = None
          LetDef(funDefWithBody, restTree)

        case ExVarDef(vs, tpt, bdy) => {
          val binderTpe = extractType(tpt.tpe)
          //binderTpe match {
          //  case ArrayType(_) => 
          //    reporter.error(tree.pos, "Cannot declare array variables, only val are alllowed")
          //    throw ImpureCodeEncounteredException(tree)
          //  case _ =>
          //}
          val newID = FreshIdentifier(vs.name.toString).setType(binderTpe)
          val valTree = extractTree(bdy)
          mutableVarSubsts += (vs -> (() => Variable(newID)))
          if(valTree.getType.isInstanceOf[ArrayType]) {
            getOwner(valTree) match {
              case None =>
                owners += (Variable(newID) -> Some(currentFunDef))
              case Some(_) =>
                reporter.error(tr.pos, "Cannot alias array")
                throw ImpureCodeEncounteredException(tr)
            }
          }
          val restTree = rest match {
            case Some(rst) => {
              varSubsts(vs) = (() => Variable(newID))
              val res = extractTree(rst)
              varSubsts.remove(vs)
              res
            }
            case None => UnitLiteral
          }

          rest = None

          LetVar(newID, valTree, restTree)
        }

        case ExAssign(sym, rhs) => mutableVarSubsts.get(sym) match {
          case Some(fun) => {
            val Variable(id) = fun()
            val rhsTree = extractTree(rhs)
            if(rhsTree.getType.isInstanceOf[ArrayType]) {
              getOwner(rhsTree) match {
                case None =>
                case Some(_) =>
                  reporter.error(tr.pos, "Cannot alias array")
                  throw ImpureCodeEncounteredException(tr)
              }
            }
            Assignment(id, rhsTree)
          }
          case None => {
            reporter.error(tr.pos, "Undeclared variable.")
            throw ImpureCodeEncounteredException(tr)
          }
        }
        case wh@ExWhile(cond, body) => {
          val condTree = extractTree(cond)
          val bodyTree = extractTree(body)
          While(condTree, bodyTree).setPosInfo(wh.pos.line,wh.pos.column)
        }
        case wh@ExWhileWithInvariant(cond, body, inv) => {
          val condTree = extractTree(cond)
          val bodyTree = extractTree(body)
          val invTree = extractTree(inv)
          val w = While(condTree, bodyTree).setPosInfo(wh.pos.line,wh.pos.column)
          w.invariant = Some(invTree)
          w
        }

        case ExInt32Literal(v) => IntLiteral(v).setType(Int32Type)
        case ExBooleanLiteral(v) => BooleanLiteral(v).setType(BooleanType)
        case ExUnitLiteral() => UnitLiteral
        case ExLocally(body) => extractTree(body)
        case ExTyped(e,tpt) => extractTree(e)
        case ExIdentifier(sym,tpt) => varSubsts.get(sym) match {
          case Some(fun) => fun()
          case None => mutableVarSubsts.get(sym) match {
            case Some(fun) => fun()
            case None => {
              reporter.error(tr.pos, "Unidentified variable.")
              throw ImpureCodeEncounteredException(tr)
            }
          }
        }
        case epsi@ExEpsilonExpression(tpe, varSym, predBody) => {
          val pstpe = extractType(tpe)
          val previousVarSubst: Option[Function0[Expr]] = varSubsts.get(varSym) //save the previous in case of nested epsilon
          varSubsts(varSym) = (() => EpsilonVariable((epsi.pos.line, epsi.pos.column)).setType(pstpe))
          val c1 = extractTree(predBody)
          previousVarSubst match {
            case Some(f) => varSubsts(varSym) = f
            case None => varSubsts.remove(varSym)
          }
          if(containsEpsilon(c1)) {
            reporter.error(epsi.pos, "Usage of nested epsilon is not allowed.")
            throw ImpureCodeEncounteredException(epsi)
          }
          Epsilon(c1).setType(pstpe).setPosInfo(epsi.pos.line, epsi.pos.column)
        }

        case chs @ ExChooseExpression(args, tpe, body, select) => {
          val cTpe  = extractType(tpe)

          val vars = args map { case (tpe, sym) =>
            val aTpe  = extractType(tpe)
            val newID = FreshIdentifier(sym.name.toString).setType(aTpe)
            owners += (Variable(newID) -> None)
            varSubsts(sym) = (() => Variable(newID))
            newID
          }

          val cBody = extractTree(body)

          Choose(vars, cBody).setType(cTpe).setPosInfo(select.pos.line, select.pos.column)
        }

        case ExWaypointExpression(tpe, i, tree) => {
          val pstpe = extractType(tpe)
          val IntLiteral(ri) = extractTree(i)
          Waypoint(ri, extractTree(tree)).setType(pstpe)
        }
        case ExCaseClassConstruction(tpt, args) => {
          val cctype = extractType(tpt.tpe)
          if(!cctype.isInstanceOf[CaseClassType]) {
            reporter.error(tr.pos, "Construction of a non-case class.")
            throw ImpureCodeEncounteredException(tr)
          }
          val nargs = args.map(extractTree(_))
          val cct = cctype.asInstanceOf[CaseClassType]
          CaseClass(cct.classDef, nargs).setType(cct)
        }

        case ExAnd(l, r) => And(extractTree(l), extractTree(r)).setType(BooleanType)
        case ExOr(l, r) => Or(extractTree(l), extractTree(r)).setType(BooleanType)
        case ExNot(e) => Not(extractTree(e)).setType(BooleanType)
        case ExUMinus(e) => UMinus(extractTree(e)).setType(Int32Type)
        case ExPlus(l, r) => Plus(extractTree(l), extractTree(r)).setType(Int32Type)
        case ExMinus(l, r) => Minus(extractTree(l), extractTree(r)).setType(Int32Type)
        case ExTimes(l, r) => Times(extractTree(l), extractTree(r)).setType(Int32Type)
        case ExDiv(l, r) => Division(extractTree(l), extractTree(r)).setType(Int32Type)
        case ExMod(l, r) => Modulo(extractTree(l), extractTree(r)).setType(Int32Type)
        case ExEquals(l, r) => {
          val rl = extractTree(l)
          val rr = extractTree(r)
          ((rl.getType,rr.getType) match {
            case (SetType(_), SetType(_)) => SetEquals(rl, rr)
            case (BooleanType, BooleanType) => Iff(rl, rr)
            case (_, _) => Equals(rl, rr)
          }).setType(BooleanType) 
        }
        case ExNotEquals(l, r) => Not(Equals(extractTree(l), extractTree(r)).setType(BooleanType)).setType(BooleanType)
        case ExGreaterThan(l, r) => GreaterThan(extractTree(l), extractTree(r)).setType(BooleanType)
        case ExGreaterEqThan(l, r) => GreaterEquals(extractTree(l), extractTree(r)).setType(BooleanType)
        case ExLessThan(l, r) => LessThan(extractTree(l), extractTree(r)).setType(BooleanType)
        case ExLessEqThan(l, r) => LessEquals(extractTree(l), extractTree(r)).setType(BooleanType)
        case ExFiniteSet(tt, args) => {
          val underlying = extractType(tt.tpe)
          FiniteSet(args.map(extractTree(_))).setType(SetType(underlying))
        }
        case ExFiniteMultiset(tt, args) => {
          val underlying = extractType(tt.tpe)
          FiniteMultiset(args.map(extractTree(_))).setType(MultisetType(underlying))
        }
        case ExEmptySet(tt) => {
          val underlying = extractType(tt.tpe)
          FiniteSet(Seq()).setType(SetType(underlying))
        }
        case ExEmptyMultiset(tt) => {
          val underlying = extractType(tt.tpe)
          EmptyMultiset(underlying).setType(MultisetType(underlying))
        }
        case ExEmptyMap(ft, tt) => {
          val fromUnderlying = extractType(ft.tpe)
          val toUnderlying   = extractType(tt.tpe)
          val tpe = MapType(fromUnderlying, toUnderlying)

          FiniteMap(Seq()).setType(tpe)
        }
        case ExLiteralMap(ft, tt, elems) => {
          val fromUnderlying = extractType(ft.tpe)
          val toUnderlying   = extractType(tt.tpe)
          val tpe = MapType(fromUnderlying, toUnderlying)

          val singletons: Seq[(Expr, Expr)] = elems.collect { case ExTuple(tpes, trees) if (trees.size == 2) =>
            (extractTree(trees(0)), extractTree(trees(1)))
          }

          if (singletons.size != elems.size) {
            reporter.error(tr.pos, "Some map elements could not be extracted as Tuple2")
            throw ImpureCodeEncounteredException(tr)
          }

          FiniteMap(singletons).setType(tpe)
        }

        case ExSetMin(t) => {
          val set = extractTree(t)
          if(!set.getType.isInstanceOf[SetType]) {
            reporter.error(t.pos, "Min should be computed on a set.")
            throw ImpureCodeEncounteredException(tr)
          }
          SetMin(set).setType(set.getType.asInstanceOf[SetType].base)
        }
        case ExSetMax(t) => {
          val set = extractTree(t)
          if(!set.getType.isInstanceOf[SetType]) {
            reporter.error(t.pos, "Max should be computed on a set.")
            throw ImpureCodeEncounteredException(tr)
          }
          SetMax(set).setType(set.getType.asInstanceOf[SetType].base)
        }
        case ExUnion(t1,t2) => {
          val rl = extractTree(t1)
          val rr = extractTree(t2)
          rl.getType match {
            case s @ SetType(_) => SetUnion(rl, rr).setType(s)
            case m @ MultisetType(_) => MultisetUnion(rl, rr).setType(m)
            case _ => {
              reporter.error(tr.pos, "Union of non set/multiset expressions.")
              throw ImpureCodeEncounteredException(tr)
            }
          }
        }
        case ExIntersection(t1,t2) => {
          val rl = extractTree(t1)
          val rr = extractTree(t2)
          rl.getType match {
            case s @ SetType(_) => SetIntersection(rl, rr).setType(s)
            case m @ MultisetType(_) => MultisetIntersection(rl, rr).setType(m)
            case _ => {
              reporter.error(tr.pos, "Intersection of non set/multiset expressions.")
              throw ImpureCodeEncounteredException(tr)
            }
          }
        }
        case ExSetContains(t1,t2) => {
          val rl = extractTree(t1)
          val rr = extractTree(t2)
          rl.getType match {
            case s @ SetType(_) => ElementOfSet(rr, rl)
            case _ => {
              reporter.error(tr.pos, ".contains on non set expression.")
              throw ImpureCodeEncounteredException(tr)
            }
          }
        }
        case ExSetSubset(t1,t2) => {
          val rl = extractTree(t1)
          val rr = extractTree(t2)
          rl.getType match {
            case s @ SetType(_) => SubsetOf(rl, rr)
            case _ => {
              reporter.error(tr.pos, "Subset on non set expression.")
              throw ImpureCodeEncounteredException(tr)
            }
          }
        }
        case ExSetMinus(t1,t2) => {
          val rl = extractTree(t1)
          val rr = extractTree(t2)
          rl.getType match {
            case s @ SetType(_) => SetDifference(rl, rr).setType(s)
            case m @ MultisetType(_) => MultisetDifference(rl, rr).setType(m)
            case _ => {
              reporter.error(tr.pos, "Difference of non set/multiset expressions.")
              throw ImpureCodeEncounteredException(tr)
            }
          }
        } 
        case ExSetCard(t) => {
          val rt = extractTree(t)
          rt.getType match {
            case s @ SetType(_) => SetCardinality(rt)
            case m @ MultisetType(_) => MultisetCardinality(rt)
            case _ => {
              reporter.error(tr.pos, "Cardinality of non set/multiset expressions.")
              throw ImpureCodeEncounteredException(tr)
            }
          }
        }
        case ExMultisetToSet(t) => {
          val rt = extractTree(t)
          rt.getType match {
            case m @ MultisetType(u) => MultisetToSet(rt).setType(SetType(u))
            case _ => {
              reporter.error(tr.pos, "toSet can only be applied to multisets.")
              throw ImpureCodeEncounteredException(tr)
            }
          }
        }
        case up@ExUpdated(m,f,t) => {
          val rm = extractTree(m)
          val rf = extractTree(f)
          val rt = extractTree(t)
          rm.getType match {
            case MapType(ft, tt) => {
              MapUnion(rm, FiniteMap(Seq((rf, rt))).setType(rm.getType)).setType(rm.getType)
            }
            case ArrayType(bt) => {
              ArrayUpdated(rm, rf, rt).setType(rm.getType).setPosInfo(up.pos.line, up.pos.column)
            }
            case _ => {
              reporter.error(tr.pos, "updated can only be applied to maps.")
              throw ImpureCodeEncounteredException(tr)
            }
          }
        }
        case ExMapIsDefinedAt(m,k) => {
          val rm = extractTree(m)
          val rk = extractTree(k)
          MapIsDefinedAt(rm, rk)
        }

        case ExPlusPlusPlus(t1,t2) => {
          val rl = extractTree(t1)
          val rr = extractTree(t2)
          MultisetPlus(rl, rr).setType(rl.getType)
        }
        case app@ExApply(lhs,args) => {
          val rlhs = extractTree(lhs)
          val rargs = args map extractTree
          rlhs.getType match {
            case MapType(_,tt) => 
              assert(rargs.size == 1)
              MapGet(rlhs, rargs.head).setType(tt).setPosInfo(app.pos.line, app.pos.column)
            case ArrayType(bt) => {
              assert(rargs.size == 1)
              ArraySelect(rlhs, rargs.head).setType(bt).setPosInfo(app.pos.line, app.pos.column)
            }
            case _ => {
              reporter.error(tr.pos, "apply on unexpected type")
              throw ImpureCodeEncounteredException(tr)
            }
          }
        }
        // for now update only occurs on Array. later we might have to distinguished depending on the type of the lhs
        case update@ExUpdate(lhs, index, newValue) => { 
          val lhsRec = extractTree(lhs)
          lhsRec match {
            case Variable(_) =>
            case _ => {
              reporter.error(tr.pos, "array update only works on variables")
              throw ImpureCodeEncounteredException(tr)
            }
          }
          getOwner(lhsRec) match {
            case Some(Some(fd)) if fd != currentFunDef => 
              reporter.error(tr.pos, "cannot update an array that is not defined locally")
              throw ImpureCodeEncounteredException(tr)
            case Some(None) =>
              reporter.error(tr.pos, "cannot update an array that is not defined locally")
              throw ImpureCodeEncounteredException(tr)
            case Some(_) =>
            case None => sys.error("This array: " + lhsRec + " should have had an owner")
          }
          val indexRec = extractTree(index)
          val newValueRec = extractTree(newValue)
          ArrayUpdate(lhsRec, indexRec, newValueRec).setPosInfo(update.pos.line, update.pos.column)
        }
        case ExArrayLength(t) => {
          val rt = extractTree(t)
          ArrayLength(rt)
        }
        case ExArrayClone(t) => {
          val rt = extractTree(t)
          ArrayClone(rt)
        }
        case ExArrayFill(baseType, length, defaultValue) => {
          val underlying = extractType(baseType.tpe)
          val lengthRec = extractTree(length)
          val defaultValueRec = extractTree(defaultValue)
          ArrayFill(lengthRec, defaultValueRec).setType(ArrayType(underlying))
        }
        case ExIfThenElse(t1,t2,t3) => {
          val r1 = extractTree(t1)
          if(containsLetDef(r1)) {
            reporter.error(t1.pos, "Condition of if-then-else expression should not contain nested function definition")
            throw ImpureCodeEncounteredException(t1)
          }
          val r2 = extractTree(t2)
          val r3 = extractTree(t3)
          val lub = leastUpperBound(r2.getType, r3.getType)
          lub match {
            case Some(lub) => IfExpr(r1, r2, r3).setType(lub)
            case None =>
              reporter.error(tr.pos, "Both branches of ifthenelse have incompatible types")
              throw ImpureCodeEncounteredException(t1)
          }
        }

        case ExIsInstanceOf(tt, cc) => {
          val ccRec = extractTree(cc)
          val checkType = extractType(tt.tpe)
          checkType match {
            case CaseClassType(ccd) => {
              val rootType: ClassTypeDef  = if(ccd.parent != None) ccd.parent.get else ccd
              if(!ccRec.getType.isInstanceOf[ClassType]) {
                reporter.error(tr.pos, "isInstanceOf can only be used with a case class")
                throw ImpureCodeEncounteredException(tr)
              } else {
                val testedExprType = ccRec.getType.asInstanceOf[ClassType].classDef
                val testedExprRootType: ClassTypeDef = if(testedExprType.parent != None) testedExprType.parent.get else testedExprType

                if(rootType != testedExprRootType) {
                  reporter.error(tr.pos, "isInstanceOf can only be used with compatible case classes")
                  throw ImpureCodeEncounteredException(tr)
                } else {
                  CaseClassInstanceOf(ccd, ccRec) 
                }
              }
            }
            case _ => {
              reporter.error(tr.pos, "isInstanceOf can only be used with a case class")
              throw ImpureCodeEncounteredException(tr)
            }
          }
        }

        case lc @ ExLocalCall(sy,nm,ar) => {
          if(defsToDefs.keysIterator.find(_ == sy).isEmpty) {
            reporter.error(tr.pos, "Invoking an invalid function.")
            throw ImpureCodeEncounteredException(tr)
          }
          val fd = defsToDefs(sy)
          FunctionInvocation(fd, ar.map(extractTree(_))).setType(fd.returnType).setPosInfo(lc.pos.line,lc.pos.column) 
        }

        case pm @ ExPatternMatching(sel, cses) => {
          val rs = extractTree(sel)
          val rc = cses.map(extractMatchCase(_))
          val rt: LeonType = rc.map(_.rhs.getType).reduceLeft(leastUpperBound(_,_).get)
          MatchExpr(rs, rc).setType(rt).setPosInfo(pm.pos.line,pm.pos.column)
        }

        // default behaviour is to complain :)
        case _ =>
          reporter.error(tr.pos, "Could not extract as PureScala.")
          throw ImpureCodeEncounteredException(tr)
      }

      rest match {
        case Some(r) =>
          LeonBlock(Seq(res), extractTree(r))
        case None =>
          res
      }
    }

    private def extractType(tpt: Type): LeonType = tpt match {
      case tpe if tpe == IntClass.tpe =>
        Int32Type

      case tpe if tpe == BooleanClass.tpe =>
        BooleanType

      case tpe if tpe == UnitClass.tpe =>
        UnitType

      case tpe if tpe == NothingClass.tpe =>
        BottomType

      case TypeRef(_, sym, btt :: Nil) if isSetTraitSym(sym) =>
        SetType(extractType(btt))

      case TypeRef(_, sym, btt :: Nil) if isMultisetTraitSym(sym) =>
        MultisetType(extractType(btt))

      case TypeRef(_, sym, List(ftt,ttt)) if isMapTraitSym(sym) =>
        MapType(extractType(ftt), extractType(ttt))

      case TypeRef(_, sym, List(t1,t2)) if isTuple2(sym) =>
        TupleType(Seq(extractType(t1),extractType(t2)))

      case TypeRef(_, sym, List(t1,t2,t3)) if isTuple3(sym) =>
        TupleType(Seq(extractType(t1),extractType(t2),extractType(t3)))

      case TypeRef(_, sym, List(t1,t2,t3,t4)) if isTuple4(sym) =>
        TupleType(Seq(extractType(t1),extractType(t2),extractType(t3),extractType(t4)))

      case TypeRef(_, sym, List(t1,t2,t3,t4,t5)) if isTuple5(sym) =>
        TupleType(Seq(extractType(t1),extractType(t2),extractType(t3),extractType(t4),extractType(t5)))

      case TypeRef(_, sym, btt :: Nil) if isArrayClassSym(sym) =>
        ArrayType(extractType(btt))

      case TypeRef(_, sym, Nil) if classesToClasses.keySet.contains(sym) =>
        classDefToClassType(classesToClasses(sym))

      case _ =>
        unsupported("Could not extract type as PureScala: ["+tpt+"]")
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

  def getReturnedExpr(expr: Expr): Seq[Expr] = expr match {
    case Let(_, _, rest) => getReturnedExpr(rest)
    case LetVar(_, _, rest) => getReturnedExpr(rest)
    case LeonBlock(_, rest) => getReturnedExpr(rest)
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
