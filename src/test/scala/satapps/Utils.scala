package satapps

import scala.util.Random

extension (r: Random) {
  def integers: LazyList[Int] = {
    LazyList.continually(r.nextInt)
  }

  def integers(exclUpper: Int): LazyList[Int] = {
    LazyList.continually(r.nextInt(exclUpper))
  }
}