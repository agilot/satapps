package satapps.problems

import Matrices.*

import org.scalatest.funsuite.AnyFunSuite

class MatricesTests extends AnyFunSuite{
  test("N-Queens"){
    assert(NQueensCompletion.decision(1, List((0, 0)))) 
    assert(!NQueensCompletion.decision(2, List((0, 0)))) 
    assert(!NQueensCompletion.decision(3, List((0, 0)))) 
    assert(!NQueensCompletion.decision(4, List((0, 0))))
    assert(NQueensCompletion.decision(5, List((0, 0)))) 
  }

  test("Blocked N-Queens"){
    assert(!BlockedNQueens.decision(1, List((0, 0)))) 
    assert(!BlockedNQueens.decision(2, List((0, 0)))) 
    assert(!BlockedNQueens.decision(3, List((0, 0)))) 
    assert(BlockedNQueens.decision(4, List((0, 0)))) 
    assert(BlockedNQueens.decision(5, List((0, 0)))) 
  }
}