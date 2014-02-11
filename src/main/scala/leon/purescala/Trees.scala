/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package purescala

import utils._

/** AST definitions for Pure Scala. */
object Trees {
  import Common._
  import TypeTrees._
  import TypeTreeOps._
  import Definitions._
  import Extractors._


  /* EXPRESSIONS */
  abstract class Expr extends Tree with Typed with Serializable with Tagged

  trait Terminal {
    self: Expr =>
  }


  /* This describes computational errors (unmatched case, taking min of an
   * empty set, division by zero, etc.). It should always be typed according to
   * the expected type. */
  case class Error(description: String) extends Expr with Terminal {
    val tags = tagsCombine(Nil, 1l << 0)
  }

  case class Choose(vars: List[Identifier], pred: Expr) extends Expr with FixedType with UnaryExtractable {

    assert(!vars.isEmpty)

    val fixedType = if (vars.size > 1) TupleType(vars.map(_.getType)) else vars.head.getType

    def extract = {
      Some((pred, (e: Expr) => Choose(vars, e).setPos(this)))
    }

    val tags = tagsCombine(pred :: vars, 1l << 1)
  }

  /* Like vals */
  case class Let(binder: Identifier, value: Expr, body: Expr) extends Expr with FixedType {
    binder.markAsLetBinder

    val fixedType = body.getType

    val tags = tagsCombine(binder :: value :: body :: Nil, 1l << 2)
  }

  case class LetTuple(binders: Seq[Identifier], value: Expr, body: Expr) extends Expr with FixedType {
    binders.foreach(_.markAsLetBinder)
    assert(value.getType.isInstanceOf[TupleType],
           "The definition value in LetTuple must be of some tuple type; yet we got [%s]. In expr: \n%s".format(value.getType, this))

    val tags = tagsCombine(List(value, body) ++ binders, 1l << 3)

    val fixedType = body.getType
  }

  case class LetDef(fd: FunDef, body: Expr) extends Expr {
    val et = body.getType
    if(et != Untyped)
      setType(et)

    val tags = tagsCombine(fd.id :: body :: Nil, 1l << 4)
  }


  /* Control flow */
  case class FunctionInvocation(tfd: TypedFunDef, args: Seq[Expr]) extends Expr with FixedType {
    val fixedType = tfd.returnType

    val tags = tagsCombine(tfd.fd.id +: args, 1l << 5)
  }

  case class IfExpr(cond: Expr, thenn: Expr, elze: Expr) extends Expr with FixedType {
    val fixedType = leastUpperBound(thenn.getType, elze.getType).getOrElse{
      AnyType
    }

    val tags = tagsCombine(List(cond, thenn, elze), 1l << 6)
  }

  case class Tuple(exprs: Seq[Expr]) extends Expr with FixedType {
    val fixedType = TupleType(exprs.map(_.getType))

    val tags = tagsCombine(exprs, 1l << 7)
  }

  object TupleSelect {
    def apply(tuple: Expr, index: Int): Expr = {
      tuple match {
        case Tuple(exprs) => exprs(index-1) // indexes as 1-based
        case _ => new TupleSelect(tuple, index)
      }
    }

    def unapply(e: TupleSelect): Option[(Expr, Int)] = {
      if (e eq null) None else Some((e.tuple, e.index))
    }
  }

  // This must be 1-indexed ! (So are methods of Scala Tuples)
  class TupleSelect(val tuple: Expr, val index: Int) extends Expr with FixedType {
    assert(index >= 1)

    assert(tuple.getType.isInstanceOf[TupleType], "Applying TupleSelect on a non-tuple tree [%s] of type [%s].".format(tuple, tuple.getType))

    val fixedType : TypeTree = tuple.getType match {
      case TupleType(ts) =>
        assert(index <= ts.size)
        ts(index - 1)

      case _ =>
        AnyType
    }

    val tags = tagsCombine(List(tuple), 1l << 8)

    override def equals(that: Any): Boolean = (that != null) && (that match {
      case t: TupleSelect => t.tuple == tuple && t.index == index
      case _ => false
    })

    override def hashCode: Int = tuple.hashCode + index.hashCode
  }

  object MatchExpr {
    def apply(scrutinee: Expr, cases: Seq[MatchCase]) : MatchExpr = {
      scrutinee.getType match {
        case a: AbstractClassType => new MatchExpr(scrutinee, cases)
        case c: CaseClassType => new MatchExpr(scrutinee, cases.filter(_.pattern match {
          case CaseClassPattern(_, cct, _) if cct.classDef != c.classDef => false
          case _ => true
        }))
        case t: TupleType => new MatchExpr(scrutinee, cases)
        case _ => scala.sys.error("Constructing match expression on non-class type.")
      }
    }

    def unapply(me: MatchExpr) : Option[(Expr,Seq[MatchCase])] = if (me == null) None else Some((me.scrutinee, me.cases))
  }

  class MatchExpr(val scrutinee: Expr, val cases: Seq[MatchCase]) extends Expr with FixedType {
    assert(cases.nonEmpty)

    val fixedType = leastUpperBound(cases.map(_.rhs.getType)).getOrElse{
      AnyType
    }

    val tags = tagsCombine(scrutinee +: cases, 1l << 9)

    def scrutineeClassType: ClassType = scrutinee.getType.asInstanceOf[ClassType]

    override def equals(that: Any): Boolean = (that != null) && (that match {
      case t: MatchExpr => t.scrutinee == scrutinee && t.cases == cases
      case _ => false
    })

    override def hashCode: Int = scrutinee.hashCode+cases.hashCode
  }

  sealed abstract class MatchCase extends Tree with Tagged {
    val pattern: Pattern
    val rhs: Expr
    val theGuard: Option[Expr]
    def hasGuard = theGuard.isDefined
    def expressions: Seq[Expr]

    val tags = tagsCombine(pattern +: expressions, 1l << 10)
  }

  case class SimpleCase(pattern: Pattern, rhs: Expr) extends MatchCase {
    val theGuard = None
    def expressions = List(rhs)
  }
  case class GuardedCase(pattern: Pattern, guard: Expr, rhs: Expr) extends MatchCase {
    val theGuard = Some(guard)
    def expressions = List(guard, rhs)
  }

  sealed abstract class Pattern extends Tree with Tagged {
    val subPatterns: Seq[Pattern]
    val binder: Option[Identifier]

    private def subBinders = subPatterns.map(_.binders).foldLeft[Set[Identifier]](Set.empty)(_ ++ _)
    def binders: Set[Identifier] = subBinders ++ (if(binder.isDefined) Set(binder.get) else Set.empty)
  }

  case class InstanceOfPattern(binder: Option[Identifier], ct: ClassType) extends Pattern { // c: Class
    val subPatterns = Seq.empty

    val tags = tagsCombine(binder.toSeq ++ subPatterns, 1l << 11)
  }
  case class WildcardPattern(binder: Option[Identifier]) extends Pattern { // c @ _
    val subPatterns = Seq.empty

    val tags = tagsCombine(binder.toSeq ++ subPatterns, 1l << 11)
  }

  case class CaseClassPattern(binder: Option[Identifier], ct: CaseClassType, subPatterns: Seq[Pattern]) extends Pattern {

    val tags = tagsCombine(binder.toSeq ++ subPatterns, 1l << 11)
  }

  case class TuplePattern(binder: Option[Identifier], subPatterns: Seq[Pattern]) extends Pattern {

    val tags = tagsCombine(binder.toSeq ++ subPatterns, 1l << 11)
  }


  /* Propositional logic */
  object And {
    def apply(l: Expr, r: Expr) : Expr = And(Seq(l, r))

    def apply(exprs: Seq[Expr]) : Expr = {
      val flat = exprs.flatMap(_ match {
        case And(es) => es
        case o => Seq(o)
      })

      var stop = false
      val simpler = for(e <- flat if !stop && e != BooleanLiteral(true)) yield {
        if(e == BooleanLiteral(false)) stop = true
        e
      }

      simpler match {
        case Seq() => BooleanLiteral(true)
        case Seq(x) => x
        case _ => new And(simpler)
      }
    }

    def unapply(and: And) : Option[Seq[Expr]] = 
      if(and == null) None else Some(and.exprs)
  }

  class And private (val exprs: Seq[Expr]) extends Expr with FixedType {
    val fixedType = BooleanType

    assert(exprs.size >= 2)

    override def equals(that: Any): Boolean = (that != null) && (that match {
      case t: And => t.exprs == exprs
      case _ => false
    })

    override def hashCode: Int = exprs.hashCode

    val tags = tagsCombine(exprs, 1l << 12)
  }

  object Or {
    def apply(l: Expr, r: Expr) : Expr = (l,r) match {
      case (BooleanLiteral(true),_)  => BooleanLiteral(true)
      case (BooleanLiteral(false),_) => r
      case (_,BooleanLiteral(false)) => l
      case _ => new Or(Seq(l,r))
    }
    def apply(exprs: Seq[Expr]) : Expr = {
      val flat = exprs.flatMap(_ match {
        case Or(es) => es
        case o => Seq(o)
      })

      var stop = false
      val simpler = for(e <- flat if !stop && e != BooleanLiteral(false)) yield {
        if(e == BooleanLiteral(true)) stop = true
        e
      }

      simpler match {
        case Seq() => BooleanLiteral(false)
        case Seq(x) => x
        case _ => new Or(simpler)
      }
    }

    def unapply(or: Or) : Option[Seq[Expr]] = 
      if(or == null) None else Some(or.exprs)
  }

  class Or(val exprs: Seq[Expr]) extends Expr with FixedType {
    val fixedType = BooleanType

    assert(exprs.size >= 2)

    override def equals(that: Any): Boolean = (that != null) && (that match {
      case t: Or => t.exprs == exprs
      case _ => false
    })

    override def hashCode: Int = exprs.hashCode

    val tags = tagsCombine(exprs, 1l << 13)
  }

  object Iff {
    def apply(left: Expr, right: Expr) : Expr = (left, right) match {
      case (BooleanLiteral(true), r) => r
      case (l, BooleanLiteral(true)) => l
      case (BooleanLiteral(false), r) => Not(r)
      case (l, BooleanLiteral(false)) => Not(l)
      case (l,r) => new Iff(l, r)  
    }

    def unapply(iff: Iff) : Option[(Expr,Expr)] = {
      if(iff != null) Some((iff.left, iff.right)) else None
    }
  }

  class Iff(val left: Expr, val right: Expr) extends Expr with FixedType {
    val fixedType = BooleanType

    override def equals(that: Any): Boolean = (that != null) && (that match {
      case t: Iff => t.left == left && t.right == right
      case _ => false
    })

    override def hashCode: Int = left.hashCode + right.hashCode

    val tags = tagsCombine(List(left, right), 1l << 14)
  }

  object Implies {
    def apply(left: Expr, right: Expr) : Expr = (left,right) match {
      case (BooleanLiteral(false), _) => BooleanLiteral(true)
      case (_, BooleanLiteral(true)) => BooleanLiteral(true)
      case (BooleanLiteral(true), r) => r
      case (l, BooleanLiteral(false)) => Not(l)
      case (l1, Implies(l2, r2)) => Implies(And(l1, l2), r2)
      case _ => new Implies(left, right)
    }
    def unapply(imp: Implies) : Option[(Expr,Expr)] =
      if(imp == null) None else Some(imp.left, imp.right)
  }

  class Implies(val left: Expr, val right: Expr) extends Expr with FixedType {
    val fixedType = BooleanType
    // if(left.getType != BooleanType || right.getType != BooleanType) {
    //   println("culprits: " + left.getType + ", " + right.getType)
    //   assert(false)
    // }

    override def equals(that: Any): Boolean = (that != null) && (that match {
      case t: Iff => t.left == left
      case _ => false
    })

    override def hashCode: Int = left.hashCode + right.hashCode

    val tags = tagsCombine(List(left, right), 1l << 15)
  }

  object Not {
    def apply(expr : Expr) : Expr = expr match {
      case Not(e) => e
      case BooleanLiteral(v) => BooleanLiteral(!v)
      case _ => new Not(expr)
    }

    def unapply(not : Not) : Option[Expr] = {
      if(not != null) Some(not.expr) else None
    }
  }

  class Not private (val expr: Expr) extends Expr with FixedType {
    val fixedType = BooleanType

    override def equals(that: Any) : Boolean = (that != null) && (that match {
      case n : Not => n.expr == expr
      case _ => false
    })

    override def hashCode : Int = expr.hashCode ^ Int.MinValue

    val tags = tagsCombine(List(expr), 1l << 16)
  }

  object Equals {
    def apply(l : Expr, r : Expr) : Expr = (l.getType, r.getType) match {
      case (BooleanType, BooleanType) => Iff(l, r)
      case _ => new Equals(l, r)
    }
    def unapply(e : Equals) : Option[(Expr,Expr)] = if (e == null) None else Some((e.left, e.right))
  }

  object SetEquals {
    def apply(l : Expr, r : Expr) : Equals = new Equals(l,r)
    def unapply(e : Equals) : Option[(Expr,Expr)] = if(e == null) None else (e.left.getType, e.right.getType) match {
      case (SetType(_), SetType(_)) => Some((e.left, e.right))
      case _ => None
    }
  }

  object MultisetEquals {
    def apply(l : Expr, r : Expr) : Equals = new Equals(l,r)
    def unapply(e : Equals) : Option[(Expr,Expr)] = if(e == null) None else (e.left.getType, e.right.getType) match {
      case (MultisetType(_), MultisetType(_)) => Some((e.left, e.right))
      case _ => None
    }
  }

  class Equals(val left: Expr, val right: Expr) extends Expr with FixedType {
    val fixedType = BooleanType

    override def equals(that: Any): Boolean = (that != null) && (that match {
      case t: Equals => t.left == left && t.right == right
      case _ => false
    })

    override def hashCode: Int = left.hashCode+right.hashCode

    val tags = tagsCombine(List(left, right), 1l << 17)
  }
  
  case class Variable(id: Identifier) extends Expr with Terminal {
    override def getType = id.getType
    override def setType(tt: TypeTree) = { id.setType(tt); this }

    val tags = tagsCombine(List(id))
  }

  /* Literals */
  sealed abstract class Literal[T] extends Expr with Terminal {
    val value: T
  }

  case class GenericValue(tp: TypeParameter, id: Int) extends Expr with Terminal with FixedType {
    val fixedType = tp

    val tags = tagsCombine(List(tp.id))
  }

  case class IntLiteral(value: Int) extends Literal[Int] with FixedType {
    val fixedType = Int32Type
    val tags = tagsCombine(Nil, 1l << 18)
  }

  case class BooleanLiteral(value: Boolean) extends Literal[Boolean] with FixedType {
    val fixedType = BooleanType
    val tags = tagsCombine(Nil, 1l << 19)
  }

  case class StringLiteral(value: String) extends Literal[String] {
    val tags = tagsCombine(Nil, 1l << 20)
  }

  case object UnitLiteral extends Literal[Unit] with FixedType {
    val fixedType = UnitType
    val value = ()

    val tags = tagsCombine(Nil, 1l << 21)
  }

  case class CaseClass(ct: CaseClassType, args: Seq[Expr]) extends Expr with FixedType {
    val fixedType = ct

    val tags = tagsCombine(ct.classDef.id +: args, 1l << 22)
  }

  case class CaseClassInstanceOf(classType: CaseClassType, expr: Expr) extends Expr with FixedType {
    val fixedType = BooleanType

    val tags = tagsCombine(classType.classDef.id :: List(expr), 1l << 23)
  }

  object CaseClassSelector {
    def apply(classType: CaseClassType, caseClass: Expr, selector: Identifier): Expr = {
      caseClass match {
        case CaseClass(ct, fields) =>
          if (ct.classDef == classType.classDef) {
            fields(ct.classDef.selectorID2Index(selector))
          } else {
            new CaseClassSelector(classType, caseClass, selector)
          }
        case _ => new CaseClassSelector(classType, caseClass, selector)
      }
    }

    def unapply(ccs: CaseClassSelector): Option[(CaseClassType, Expr, Identifier)] = {
      Some((ccs.classType, ccs.caseClass, ccs.selector))
    }
  }

  class CaseClassSelector(val classType: CaseClassType, val caseClass: Expr, val selector: Identifier) extends Expr with FixedType {
    val fixedType = classType.fieldsTypes(classType.classDef.selectorID2Index(selector))

    override def equals(that: Any): Boolean = (that != null) && (that match {
      case t: CaseClassSelector => (t.classType, t.caseClass, t.selector) == (classType, caseClass, selector)
      case _ => false
    })

    override def hashCode: Int = (classType, caseClass, selector).hashCode

    val tags = tagsCombine(classType.classDef.id :: List(caseClass, selector), 1l << 24)
  }

  /* Arithmetic */
  case class Plus(lhs: Expr, rhs: Expr) extends Expr with FixedType {
    val fixedType = Int32Type

    val tags = tagsCombine(List(lhs, rhs), 1l << 25)
  }
  case class Minus(lhs: Expr, rhs: Expr) extends Expr with FixedType { 
    val fixedType = Int32Type

    val tags = tagsCombine(List(lhs, rhs), 1l << 26)
  }
  case class UMinus(expr: Expr) extends Expr with FixedType { 
    val fixedType = Int32Type

    val tags = tagsCombine(List(expr), 1l << 27)
  }
  case class Times(lhs: Expr, rhs: Expr) extends Expr with FixedType { 
    val fixedType = Int32Type

    val tags = tagsCombine(List(lhs, rhs), 1l << 28)
  }
  case class Division(lhs: Expr, rhs: Expr) extends Expr with FixedType { 
    val fixedType = Int32Type

    val tags = tagsCombine(List(lhs, rhs), 1l << 29)
  }
  case class Modulo(lhs: Expr, rhs: Expr) extends Expr with FixedType { 
    val fixedType = Int32Type

    val tags = tagsCombine(List(lhs, rhs), 1l << 30)
  }
  case class LessThan(lhs: Expr, rhs: Expr) extends Expr with FixedType { 
    val fixedType = BooleanType

    val tags = tagsCombine(List(lhs, rhs), 1l << 31)
  }
  case class GreaterThan(lhs: Expr, rhs: Expr) extends Expr with FixedType { 
    val fixedType = BooleanType

    val tags = tagsCombine(List(lhs, rhs), 1l << 32)
  }
  case class LessEquals(lhs: Expr, rhs: Expr) extends Expr with FixedType { 
    val fixedType = BooleanType

    val tags = tagsCombine(List(lhs, rhs), 1l << 33)
  }
  case class GreaterEquals(lhs: Expr, rhs: Expr) extends Expr with FixedType {
    val fixedType = BooleanType

    val tags = tagsCombine(List(lhs, rhs), 1l << 34)
  }

  /* Set expressions */
  case class FiniteSet(elements: Seq[Expr]) extends Expr {
    val tpe = if (elements.isEmpty) None else leastUpperBound(elements.map(_.getType))
    tpe.foreach(t => setType(SetType(t)))

    val tags = tagsCombine(elements, 1l << 35)
  }
  // TODO : Figure out what evaluation order is, for this.
  // Perhaps then rewrite as "contains".
  case class ElementOfSet(element: Expr, set: Expr) extends Expr with FixedType {
    val fixedType = BooleanType

    val tags = tagsCombine(List(element, set), 1l << 36)
  }
  case class SetCardinality(set: Expr) extends Expr with FixedType {
    val fixedType = Int32Type

    val tags = tagsCombine(List(set), 1l << 37)
  }
  case class SubsetOf(set1: Expr, set2: Expr) extends Expr with FixedType {
    val fixedType = BooleanType

    val tags = tagsCombine(List(set1, set2), 1l << 38)
  }

  case class SetIntersection(set1: Expr, set2: Expr) extends Expr {
    leastUpperBound(Seq(set1, set2).map(_.getType)).foreach(setType _)

    val tags = tagsCombine(List(set1, set2), 1l << 39)
  }
  case class SetUnion(set1: Expr, set2: Expr) extends Expr {
    leastUpperBound(Seq(set1, set2).map(_.getType)).foreach(setType _)

    val tags = tagsCombine(List(set1, set2), 1l << 40)
  }
  case class SetDifference(set1: Expr, set2: Expr) extends Expr {
    leastUpperBound(Seq(set1, set2).map(_.getType)).foreach(setType _)

    val tags = tagsCombine(List(set1, set2), 1l << 41)
  }
  case class SetMin(set: Expr) extends Expr with FixedType with NoTag {
    val fixedType = Int32Type
  }
  case class SetMax(set: Expr) extends Expr with FixedType with NoTag {
    val fixedType = Int32Type
  }

  /* Multiset expressions */
  case class EmptyMultiset(baseType: TypeTree) extends Expr with Terminal with NoTag
  case class FiniteMultiset(elements: Seq[Expr]) extends Expr with NoTag 
  case class Multiplicity(element: Expr, multiset: Expr) extends Expr with NoTag 
  case class MultisetCardinality(multiset: Expr) extends Expr with FixedType with NoTag {
    val fixedType = Int32Type
  }
  case class SubmultisetOf(multiset1: Expr, multiset2: Expr) extends Expr with NoTag
  case class MultisetIntersection(multiset1: Expr, multiset2: Expr) extends Expr with NoTag
  case class MultisetUnion(multiset1: Expr, multiset2: Expr) extends Expr with NoTag
  case class MultisetPlus(multiset1: Expr, multiset2: Expr) extends Expr with NoTag // disjoint union
  case class MultisetDifference(multiset1: Expr, multiset2: Expr) extends Expr with NoTag
  case class MultisetToSet(multiset: Expr) extends Expr with NoTag

  /* Map operations. */
  case class FiniteMap(singletons: Seq[(Expr, Expr)]) extends Expr with NoTag

  case class MapGet(map: Expr, key: Expr) extends Expr with NoTag
  case class MapUnion(map1: Expr, map2: Expr) extends Expr with NoTag
  case class MapDifference(map: Expr, keys: Expr) extends Expr with NoTag
  case class MapIsDefinedAt(map: Expr, key: Expr) extends Expr with FixedType with NoTag {
    val fixedType = BooleanType
  }

  /* Array operations */
  case class ArrayFill(length: Expr, defaultValue: Expr) extends Expr with FixedType with NoTag {
    val fixedType = ArrayType(defaultValue.getType)
  }

  case class ArrayMake(defaultValue: Expr) extends Expr with FixedType with NoTag {
    val fixedType = ArrayType(defaultValue.getType)
  }

  case class ArraySelect(array: Expr, index: Expr) extends Expr with FixedType with NoTag {
    assert(array.getType.isInstanceOf[ArrayType],
           "The array value in ArraySelect must of of array type; yet we got [%s]. In expr: \n%s".format(array.getType, array))

    val fixedType = array.getType match {
      case ArrayType(base) =>
        base
      case _ =>
        AnyType
    }

  }

  case class ArrayUpdated(array: Expr, index: Expr, newValue: Expr) extends Expr with FixedType with NoTag {
    assert(array.getType.isInstanceOf[ArrayType],
           "The array value in ArrayUpdated must of of array type; yet we got [%s]. In expr: \n%s".format(array.getType, array))

    val fixedType = array.getType match {
      case ArrayType(base) =>
        leastUpperBound(base, newValue.getType).map(ArrayType(_)).getOrElse(AnyType)
      case _ =>
        AnyType
    }
  }

  case class ArrayLength(array: Expr) extends Expr with FixedType with NoTag {
    val fixedType = Int32Type
  }
  case class FiniteArray(exprs: Seq[Expr]) extends Expr with NoTag
  case class ArrayClone(array: Expr) extends Expr  with NoTag{
    if(array.getType != Untyped)
      setType(array.getType)
  }

  /* List operations */
  case class NilList(baseType: TypeTree) extends Expr with Terminal with NoTag
  case class Cons(head: Expr, tail: Expr) extends Expr  with NoTag
  case class Car(list: Expr) extends Expr  with NoTag
  case class Cdr(list: Expr) extends Expr  with NoTag
  case class Concat(list1: Expr, list2: Expr) extends Expr  with NoTag
  case class ListAt(list: Expr, index: Expr) extends Expr with NoTag

  /* Constraint programming */
  case class Distinct(exprs: Seq[Expr]) extends Expr with FixedType with NoTag {
    val fixedType = BooleanType
  }

}
