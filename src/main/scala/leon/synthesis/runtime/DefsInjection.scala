/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package synthesis
package runtime

import java.io.{ObjectOutputStream, FileOutputStream, File}
import purescala.Trees._
import purescala.Definitions._
import purescala.Common._
import purescala.TypeTrees._
import purescala.ScalaPrinter
import purescala.Definitions.{Program, FunDef}

object DefsInjectionPhase extends LeonPhase[Program, Unit] {
  val name        = "Defs Injection"
  val description = "Injection of definitions to runtime"

  def run(ctx: LeonContext)(p: Program): Unit = {
    val options = SynthesisPhase.processOptions(ctx)

    var chooses = ChooseInfo.extractFromProgram(ctx, p, options)

    // Generate random file with serialized data
    val fName = "leon_"+p.mainObject.id.name+".obj"

    val oos = new ObjectOutputStream(new FileOutputStream(new File(fName)))
    oos.writeObject(p)
    oos.close

    // Generate fake FunDef to mock call to internal runtime init
    val initFunDef = new FunDef(FreshIdentifier("leon.synthesis.runtime.RuntimeSynthesis.init"),
                                UnitType,
                                Seq(VarDecl(FreshIdentifier("name"), StringType)))

    // Initialize the runtime synthesis engine with relevant info:
    val runtimeVal = ValDef(VarDecl(FreshIdentifier("__runtimeInit"), UnitType),
                            FunctionInvocation(initFunDef, Seq(StringLiteral(fName))))

    val newP = p.copy(mainObject = p.mainObject.copy(defs = runtimeVal +: p.mainObject.defs))

    println(ScalaPrinter(newP))
  }


}
