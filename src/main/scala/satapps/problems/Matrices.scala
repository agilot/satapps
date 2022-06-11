package satapps.problems

import satapps.*
import ConstrProg.{*, given}
import Extensions.*
import z3.scala.Z3AST

object Matrices {

  private def filterCells(q: NumQuery): Set[(Int, Int)] = q.toInt.filterPositive.varSet.map{case s"${v1},${v2}"=> (v1.toInt, v2.toInt)}
  private def grid(n: Int, m: Int): Seq[(Int, Int)] = Iter.cartesian(Range(0, n), Range(0, m)).toSeq

  object LatinSquare extends BiProblem[Int, Iterable[(Int, Int, Int)], Matrix[Int]]{
    def constraints(n: Int, constr: Iterable[(Int, Int, Int)]) = latinSquareConstraints(n, constr)
    def convert(n: Int, constr: Iterable[(Int, Int, Int)], sol: NumQuery) = Matrix(sol.toInt.query(grid(n, n).map((i, j) => s"${i},${j}")).toIndexedSeq, n, n)
    def verify(n: Int, constr: Iterable[(Int, Int, Int)], sol: Matrix[Int]) = ???
  }

  object Sudoku extends BiProblem[Int, Iterable[(Int, Int, Int)], Matrix[Int]]{
    def constraints(k: Int, constr: Iterable[(Int, Int, Int)]) =
      val n = k * k
      val cst: BoolConstr = And(for(ci <- 0 until k; cj <- 0 until k)
        yield IntDist((for(i <- ci * k until (ci + 1) * k; j <- cj * k until (cj + 1) * k)
        yield IntVar((i, j))).toList))
      latinSquareConstraints(n, constr) && cst
    def convert(k: Int, constr: Iterable[(Int, Int, Int)], sol: NumQuery) = Matrix(sol.toInt.query(grid(k * k, k * k).map((v1, v2) => s"${v1},${v2}")).toIndexedSeq, k * k, k * k)
    def verify(n: Int, constr: Iterable[(Int, Int, Int)], sol: Matrix[Int]) = ???
  }

  object NQueensCompletion extends BiProblem[Int, Iterable[(Int, Int)], Set[(Int, Int)]]{
    def constraints(n: Int, constr: Iterable[(Int, Int)]) =    
      val cst: BoolConstr = constr.map(c => IntVar(c)).toList === 1
      nQueensConstraints(n) && cst
    def convert(n: Int, constr: Iterable[(Int, Int)], sol: NumQuery) = filterCells(sol)
    def verify(n: Int, constr: Iterable[(Int, Int)], sol: Set[(Int, Int)]) = ???
  }
  
  object BlockedNQueens extends BiProblem[Int, Iterable[(Int, Int)], Set[(Int, Int)]]{
    def constraints(n: Int, constr: Iterable[(Int, Int)]) =    
      val cst: BoolConstr = constr.map(c => IntVar(c)).toList === 0
      nQueensConstraints(n) && cst
    def convert(n: Int, constr: Iterable[(Int, Int)], sol: NumQuery) = filterCells(sol)
    def verify(n: Int, constr: Iterable[(Int, Int)], sol: Set[(Int, Int)]) = ???
  }

  private def latinSquareConstraints(n: Int, constr: Iterable[(Int, Int, Int)]): BoolConstr =
    val vars: Seq[IntConstr] = IntVar(grid(n, n))
    val cst1: BoolConstr = vars >= 0 && vars <= n
    val cst2: BoolConstr = And(constr.map((i, j, v) => IntVar((i, j)) === v).toList)
    val cst3: BoolConstr = And(for(i <- 0 until n) yield IntDist(for(j <- 0 until n) yield IntVar((i, j))))
    val cst4: BoolConstr = And(for(j <- 0 until n) yield IntDist(for(i <- 0 until n) yield IntVar((i, j))))
    And(List(cst1, cst2, cst3, cst4))

  private def nQueensConstraints(n: Int, q: Int): BoolConstr = 
    val vars: Seq[IntConstr] = IntVar(grid(n, n))
    val cst1: BoolConstr = vars >= 0 && Add(vars) >= q
    val cst2: BoolConstr = And(for(i <- 0 until n) yield Add(for(j <- 0 until n) yield IntVar((i, j))) <= 1)
    val cst3: BoolConstr = And(for(j <- 0 until n) yield Add(for(i <- 0 until n) yield IntVar((i, j))) <= 1)
    val cst4: BoolConstr = And(for(j <- 0 until 2 * n - 1)
      yield Add(for(i <- 0 until n; if (0 <= j - i && j - i < n)) yield IntVar((n - 1 - i, j - i))) <= 1)
    val cst5: BoolConstr = And(for(i <- 0 until 2 * n - 1)
      yield Add(for(j <- 0 until n; if (0 <= i - j && i - j < n)) yield IntVar((j, i - j))) <= 1)
    And(List(cst1, cst2, cst3, cst4, cst5))

  private def nQueensConstraints(n: Int): BoolConstr = 
    nQueensConstraints(n, n)

}