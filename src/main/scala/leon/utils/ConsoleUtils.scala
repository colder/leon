package leon.utils

object ConsoleUtils {

    def ask[T](prompt: String, convert: String => Option[T]): T = {
      var res: Option[T] = None
      do {
          print(prompt)
          res = try {
            convert(readLine())
          } catch {
            case e: Throwable =>
              None
          }
      } while(res.isEmpty)

      res.get
    }

    def askAlternatives[T](prompt: String, alts: Seq[T], printer: T => String): T = {
      var res: Option[T] = None
      do {
          println("Alternatives: ")
          alts.zipWithIndex.foreach { case (a, i) =>
            println(" "+(i+1)+": "+printer(a))
          }

          val i = try {
            print(prompt)
            readLine().toInt
          } catch {
            case e: Throwable =>
              0
          }

          if (i > 0 && i <= alts.size) {
            res = Some(alts(i-1))
          }
      } while(res.isEmpty)

      res.get
    }
}
