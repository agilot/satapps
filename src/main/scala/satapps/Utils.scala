package satapps

def min[T](start: T, idx: Int, prob: Int => Option[T], endIdx: Int): T =
  def rec(last: T, k: Int): T =
    val sol: Option[T] = prob(k)
    sol match {
      case Some(s) if k > endIdx => rec(s, k - 1)
      case _ => last
    }
    
  rec(start, idx)

def max[T](start: T, idx: Int, prob: Int => Option[T], endIdx: Int): T =
  def rec(last: T, k: Int): T =
    val sol: Option[T] = prob(k)
    sol match {
      case Some(s) if k < endIdx => rec(s, k + 1)
      case _ => last
    }
    
  rec(start, idx)

