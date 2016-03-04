/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package grammars

import purescala.Types._
import purescala.Expressions._
import purescala.Constructors._

case class Label(
  tpe: TypeTree,
  cost: Int,
  exprs: Set[Expr] = Set()
) extends Typed {
  val getType = tpe

  def asString(implicit ctx: LeonContext): String = {
    val ts = tpe.asString
    val oc = "|"+cost+"|"
    val es = if(exprs.nonEmpty) {
      exprs.map(_.asString).mkString("{",",","}")
    } else {
      ""
    }

    ts + oc + es
  }
}
