package leon.verification.utils

import leon._
import leon.purescala.Definitions._
import leon.purescala.Trees._
import leon.purescala.TreeOps._
import leon.solvers.z3._
import leon.solvers.Solver

import java.util.Date
import java.text.SimpleDateFormat

import sys.process._

import java.io.File

object Benchmarks extends App {

  // Parse arguments
  val (options, others) = args.partition(_.startsWith("--"))

  println("# Date: "+new SimpleDateFormat("dd.MM.yyyy HH:mm:ss").format(new Date()))
  println("# Git tree: "+("git log -1 --format=\"%H\"".!!).trim)
  println("# Options: "+options.mkString(" "))


  val infoSep    : String = "╟" + ("┄" * 86) + "╢"
  val infoFooter : String = "╚" + ("═" * 86) + "╝"
  val infoHeader : String = "  ┌────────────┐\n" +
                            "╔═╡ Benchmarks ╞" + ("═" * 71) + "╗\n" +
                            "║ └────────────┘" + (" " * 71) + "║"

  def infoLine(file: String, f: String, kind: String, ts: String) : String = {
    "║ %-30s %-24s %19s %5s ms ║".format(
      file,
      f,
      kind,
      ts)
  }

  println(infoHeader)

  var nSuccessTotal, nInnapTotal, nDecompTotal, nAltTotal = 0
  var tTotal: Long = 0

  val ctx = leon.Main.processOptions(new SilentReporter, args)

  for (file <- ctx.files) {
    val innerCtx = ctx.copy(files = List(file))

    val pipeline = leon.plugin.ExtractionPhase andThen verification.AnalysisPhase

    val vr = pipeline.run(innerCtx)(file.getPath :: Nil)

    for (vc <- vr.conditions) {
      val timeStr = vc.time match {
        case Some(d) =>
          tTotal += (d*1000).toLong
          "%5d".format((d*1000).toLong)
        case None =>
          "?"
      }

      println(infoLine(file.getName().toString, vc.funDef.id.toString, vc.kind.toString, timeStr))
    }

    println(infoSep)

  }

  println(infoLine("TOTAL", "", "", "%5d".format(tTotal)))

  println(infoFooter)

  println

  val infoHeader2 : String = "  ┌────────────┐\n" +
                             "╔═╡ Timers     ╞" + ("═" * 71) + "╗\n" +
                             "║ └────────────┘" + (" " * 71) + "║"

  println(infoHeader2)
  for ((name, sw) <- StopwatchCollections.getAll.toSeq.sortBy(_._1)) {
    println("║ %-70s %10s ms ║".format(name, sw.getMillis))
  }
  println(infoFooter)
}
