package satapps.problems

import Matrices.*

import org.scalatest.funsuite.AnyFunSuite

class MatricesTests extends AnyFunSuite{
  test("N-Queens"){
    assert(NQueensCompletion.decide(1, List((0, 0)))) 
    assert(!NQueensCompletion.decide(2, List((0, 0)))) 
    assert(!NQueensCompletion.decide(3, List((0, 0)))) 
    assert(!NQueensCompletion.decide(4, List((0, 0))))
    assert(NQueensCompletion.decide(5, List((0, 0)))) 
  }

  test("Blocked N-Queens"){
    assert(!BlockedNQueens.decide(1, List((0, 0)))) 
    assert(!BlockedNQueens.decide(2, List((0, 0)))) 
    assert(!BlockedNQueens.decide(3, List((0, 0)))) 
    assert(BlockedNQueens.decide(4, List((0, 0)))) 
    assert(BlockedNQueens.decide(5, List((0, 0)))) 
  }
}