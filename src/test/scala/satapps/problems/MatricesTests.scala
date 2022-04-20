package satapps.problems

import Matrices.*

import org.scalatest.funsuite.AnyFunSuite

class MatricesTests extends AnyFunSuite{
  test("N-Queens"){
    assert(nQueensCompletion(1, List((0, 0))).isDefined) 
    assert(!nQueensCompletion(2, List((0, 0))).isDefined) 
    assert(!nQueensCompletion(3, List((0, 0))).isDefined) 
    assert(!nQueensCompletion(4, List((0, 0))).isDefined)
    assert(nQueensCompletion(5, List((0, 0))).isDefined) 
  }

  test("Blocked N-Queens"){
    assert(!blockedNQueens(1, List((0, 0))).isDefined) 
    assert(!blockedNQueens(2, List((0, 0))).isDefined) 
    assert(!blockedNQueens(3, List((0, 0))).isDefined) 
    assert(blockedNQueens(4, List((0, 0))).isDefined) 
    assert(blockedNQueens(5, List((0, 0))).isDefined) 
  }
}