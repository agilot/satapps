package satapps.problems

import satapps.*
import Z3.{*, given}
import Extensions.*
import z3.scala.Z3AST

object Matrices {

  object LatinSquare extends BiProblem[Int, Iterable[(Int, Int, Int)], Matrix[Int]]{
    def constraints(n: Int, constr: Iterable[(Int, Int, Int)]) =
      val str: IndexedSeq[String] = for(i <- 0 until n; j <- 0 until n) yield s"${i},${j}"
      (latinSquareConstraints(n, constr), str)
    def convert(n: Int, constr: Iterable[(Int, Int, Int)], sol: Seq[Z3AST]) = Matrix(toInt(sol).toIndexedSeq, n, n)
  }

  object Sudoku extends BiProblem[Int, Iterable[(Int, Int, Int)], Matrix[Int]]{
    def constraints(k: Int, constr: Iterable[(Int, Int, Int)]) =
      val n = k * k
      val str: Seq[String] = for(i <- 0 until n; j <- 0 until n) yield s"${i},${j}"
      val cst: Z3Type = andAll(for(ci <- 0 until k; cj <- 0 until k)
        yield distinct((for(i <- ci * k until (ci + 1) * k; j <- cj * k until (cj + 1) * k)
        yield intConst(s"${i},${j}")).toList))
      (latinSquareConstraints(n, constr) && cst, str)
    def convert(k: Int, constr: Iterable[(Int, Int, Int)], sol: Seq[Z3AST]) = Matrix(toInt(sol).toIndexedSeq, k * k, k * k)
  }

  object NQueensCompletion extends BiProblem[Int, Iterable[(Int, Int)], Set[(Int, Int)]]{
    def constraints(n: Int, constr: Iterable[(Int, Int)]) =    
      val str: Seq[String] = for(i <- 0 until n; j <- 0 until n) yield s"${i},${j}"
      val cst: Z3Type = constr.map((i, j) => intConst(s"${i},${j}")).toList === 1
      (nQueensConstraints(n) && cst, str)
    def convert(n: Int, constr: Iterable[(Int, Int)], sol: Seq[Z3AST]) = 
      toInt(sol).zipWithIndex.filter((cs, idx) => cs > 0).map((cs, idx) => (idx / n, idx % n)).toSet
  }
  
  object BlockedNQueens extends BiProblem[Int, Iterable[(Int, Int)], Set[(Int, Int)]]{
    def constraints(n: Int, constr: Iterable[(Int, Int)]) =    
      val str: Seq[String] = for(i <- 0 until n; j <- 0 until n) yield s"${i},${j}"
      val cst: Z3Type = constr.map((i, j) => intConst(s"${i},${j}")).toList === 0
      (nQueensConstraints(n) && cst, str)
    def convert(n: Int, constr: Iterable[(Int, Int)], sol: Seq[Z3AST]) = 
      toInt(sol).zipWithIndex.filter((cs, idx) => cs > 0).map((cs, idx) => (idx / n, idx % n)).toSet
  }

  private def latinSquareConstraints(n: Int, constr: Iterable[(Int, Int, Int)]): Z3Type =
    val str: Seq[String] = for(i <- 0 until n; j <- 0 until n) yield s"${i},${j}"
    val vars: Seq[Z3Type] = intConst(str)

    val cst1: Z3Type = vars >= 0 && vars <= n
    val cst2: Z3Type = andAll(constr.map((i, j, v) => intConst(s"${i},${j}") === v).toList)
    val cst3: Z3Type = andAll(for(i <- 0 until n) yield distinct(for(j <- 0 until n) yield intConst(s"${i},${j}")))
    val cst4: Z3Type = andAll(for(j <- 0 until n) yield distinct(for(i <- 0 until n) yield intConst(s"${i},${j}")))
    andAll(List(cst1, cst2, cst3, cst4))

  private def nQueensConstraints(n: Int, q: Int): Z3Type = 
    val str: Seq[String] = for(i <- 0 until n; j <- 0 until n) yield s"${i},${j}"
    val vars: Seq[Z3Type] = intConst(str)
    val cst1: Z3Type = vars >= 0 && sum(vars) >= q
    val cst2: Z3Type = andAll(for(i <- 0 until n) yield sum(for(j <- 0 until n) yield intConst(s"${i},${j}")) <= 1)
    val cst3: Z3Type = andAll(for(j <- 0 until n) yield sum(for(i <- 0 until n) yield intConst(s"${i},${j}")) <= 1)
    val cst4: Z3Type = andAll(for(j <- 0 until 2 * n - 1)
      yield sum(for(i <- 0 until n; if (0 <= j - i && j - i < n)) yield intConst(s"${n - 1 - i},${j - i}")) <= 1)
    val cst5: Z3Type = andAll(for(i <- 0 until 2 * n - 1)
      yield sum(for(j <- 0 until n; if (0 <= i - j && i - j < n)) yield intConst(s"${j},${i - j}")) <= 1)
    andAll(List(cst1, cst2, cst3, cst4, cst5))

  private def nQueensConstraints(n: Int): Z3Type = 
    nQueensConstraints(n, n)

}