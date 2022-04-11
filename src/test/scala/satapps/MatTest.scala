package satapps

import org.scalatest.funsuite.AnyFunSuite

class MatTest extends AnyFunSuite{
  test("N-Queens"){
    assert(Mat.nQueensCompletion(1, List((0, 0))).isDefined) 
    assert(!Mat.nQueensCompletion(2, List((0, 0))).isDefined) 
    assert(!Mat.nQueensCompletion(3, List((0, 0))).isDefined) 
    assert(!Mat.nQueensCompletion(4, List((0, 0))).isDefined)
    assert(Mat.nQueensCompletion(5, List((0, 0))).isDefined) 
  }

  test("Blocked N-Queens"){
    assert(!Mat.blockedNQueens(1, List((0, 0))).isDefined) 
    assert(!Mat.blockedNQueens(2, List((0, 0))).isDefined) 
    assert(!Mat.blockedNQueens(3, List((0, 0))).isDefined) 
    assert(Mat.blockedNQueens(4, List((0, 0))).isDefined) 
    assert(Mat.blockedNQueens(5, List((0, 0))).isDefined) 
  }
}