/* Copyright 2009-2016 EPFL, Lausanne */

import leon.lang._
import leon.collection._
import leon.lang.synthesis._

object Holes {
  def abs3(a: BigInt) = {
    if (?(a > 0, a < 0)) {
      a
    } else {
      -a
    }
  } ensuring {
    _ >= 0
  }
}
