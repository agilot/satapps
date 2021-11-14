package satapps

import org.scalatest.funsuite.AnyFunSuite
import scala.language.implicitConversions

class MatTest extends AnyFunSuite{
  test("N-Queens"){
    val n = 8
    assert(Mat.nQueens(1, DPLL, Nil)) 
    assert(!Mat.nQueens(2, DPLL, Nil)) 
    assert(!Mat.nQueens(3, DPLL, Nil)) 
    for(i <- 4 to n){
      assert(Mat.nQueens(i, DPLL, Nil)) 
    }
  }
}