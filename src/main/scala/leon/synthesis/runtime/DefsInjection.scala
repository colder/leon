/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package synthesis
package runtime

import java.io.{ObjectOutputStream, FileOutputStream, File}
import purescala.Trees._
import purescala.TreeOps._
import purescala.Definitions._
import purescala.Common._
import purescala.TypeTrees._
import purescala.ScalaPrinter
import purescala.Definitions.{Program, FunDef}

object DefsInjectionPhase extends LeonPhase[Program, Unit] {
  val name        = "Defs Injection"
  val description = "Injection of definitions to runtime"

  def run(ctx: LeonContext)(p: Program): Unit = {
    // Generate random file with serialized data
    val fName = "leon_"+p.mainObject.id.name+".obj"

    val oos = new ObjectOutputStream(new FileOutputStream(new File(fName)))
    oos.writeObject(p)
    oos.writeObject(UniqueCounter.nextGlobal)
    oos.close

    // Generate fake FunDef to mock call to internal runtime init

    val onChoose = new FunDef(FreshIdentifier("leon.synthesis.runtime.RuntimeSynthesis.onChoose"),
                                AnyType,
                                Seq(
                                  VarDecl(FreshIdentifier("file"), StringType),
                                  VarDecl(FreshIdentifier("line"), Int32Type),
                                  VarDecl(FreshIdentifier("map"), MapType(StringType, AnyType))
                                ))


    def interceptChooses(e: Expr): Option[Expr] = e match {
      case c @ Choose(vars, phi) =>
        
        val inputVars = variablesOf(phi) -- vars.toSet

        val fcall = FunctionInvocation(onChoose, Seq(
                                              StringLiteral(fName),
                                              IntLiteral(c.posIntInfo._1),
                                              FiniteMap(
                                                inputVars.map(v => StringLiteral(v.name.toString) -> Variable(v)).toSeq
                                              ).setType(MapType(StringType, AnyType))
                                          )
                                      )

        Some(AsInstanceOf(fcall, c.getType))
      case _ => None
    }

    p.definedFunctions.foreach { fd =>
        fd.body = fd.body.map( searchAndReplaceDFS(interceptChooses)_ )
    }

    println("import leon.Utils._")
    println(ScalaPrinter(p))
  }


}
