package satapps

import org.scalatest.funsuite.AnyFunSuite
import problems.Matrices

class MatricesTest extends AnyFunSuite{
  test("N-Queens"){
    assert(Matrices.nQueensCompletion(1, List((0, 0))).isDefined) 
    assert(!Matrices.nQueensCompletion(2, List((0, 0))).isDefined) 
    assert(!Matrices.nQueensCompletion(3, List((0, 0))).isDefined) 
    assert(!Matrices.nQueensCompletion(4, List((0, 0))).isDefined)
    assert(Matrices.nQueensCompletion(5, List((0, 0))).isDefined) 
  }

  test("Blocked N-Queens"){
    assert(!Matrices.blockedNQueens(1, List((0, 0))).isDefined) 
    assert(!Matrices.blockedNQueens(2, List((0, 0))).isDefined) 
    assert(!Matrices.blockedNQueens(3, List((0, 0))).isDefined) 
    assert(Matrices.blockedNQueens(4, List((0, 0))).isDefined) 
    assert(Matrices.blockedNQueens(5, List((0, 0))).isDefined) 
  }
}