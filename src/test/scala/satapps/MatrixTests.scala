package satapps

import org.scalatest.funsuite.AnyFunSuite

class MatrixTests extends AnyFunSuite {
  val m = Matrix(
    Seq( 1, 2, 3 ),
    Seq( 4, 5, 6 )
  )

  val s = Matrix(
    Seq( 1, 2, 3 ),
    Seq( 4, 5, 6 )
  )

  val o = Matrix(
    Seq( 1, 2, 4 ),
    Seq( 4, 5, 6 )
  )

  val t = Matrix(
    Seq( 1, 4 ),
    Seq( 2, 5 ),
    Seq( 3, 6 )
  )

  test("unravel") {
    assert(
      m.unravel 
      ==
      IndexedSeq(1, 2, 3, 4, 5, 6)
    )
  }

  test("apply") {
    for(v <- 0 until 6) {
      val i =  v / 3
      val j = v % 3
      assert( m(i, j) == (v + 1) )
    }
  }

  test("toString") {
    assert(
      m.toString
      ==
      "1 2 3\n4 5 6"
    )
  }

  test("equals") {
    assert( m == m )
    assert( m == s )
    assert( m != o )
    assert( m != t )
  }

  test("Horizontal concatenation") {
    assert(
      m.hConcatenate(o)
      ==
      Matrix(
        Seq( 1, 2, 3, 1, 2, 4 ),
        Seq( 4, 5, 6, 4, 5, 6 )
      )
    )
  }

  test("Vertical concatenation") {
    assert(
      m.vConcatenate(o)
      ==
      Matrix(
        Seq( 1, 2, 3 ),
        Seq( 4, 5, 6 ),
        Seq( 1, 2, 4 ),
        Seq( 4, 5, 6 )
      )
    )
  }
}