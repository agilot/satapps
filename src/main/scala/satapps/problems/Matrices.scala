package satapps.problems

import satapps.*
import Z3.{*, given}
import Extensions.*

object Matrices {

  private def latinSquareConstraints(n: Int, constr: Iterable[(Int, Int, Int)]): Z3Type =
    val str: Seq[String] = for(i <- 0 until n; j <- 0 until n) yield s"${i},${j}"
    val vars: Seq[Z3Type] = intConst(str)

    val cst1: Z3Type = vars >= 0 && vars <= n
    val cst2: Z3Type = andAll(constr.map((i, j, v) => intConst(s"${i},${j}") === v).toList)
    val cst3: Z3Type = andAll(for(i <- 0 until n) yield distinct(for(j <- 0 until n) yield intConst(s"${i},${j}")))
    val cst4: Z3Type = andAll(for(j <- 0 until n) yield distinct(for(i <- 0 until n) yield intConst(s"${i},${j}")))
    andAll(List(cst1, cst2, cst3, cst4))

  def latinSquare(n: Int, constr: Iterable[(Int, Int, Int)]): Option[Matrix[Int]] = 
    val str: IndexedSeq[String] = for(i <- 0 until n; j <- 0 until n) yield s"${i},${j}"
    val (sol, z) = solve(latinSquareConstraints(n, constr), str)
    val res = toInt(sol).map(s => Matrix(s.toIndexedSeq, n, n))
    z.delete()
    res

  def sudoku(k: Int, constr: Iterable[(Int, Int, Int)]): Option[Matrix[Int]] = 
    val n = k * k
    val str: Seq[String] = for(i <- 0 until n; j <- 0 until n) yield s"${i},${j}"
    val cst: Z3Type = andAll(for(ci <- 0 until k; cj <- 0 until k)
      yield distinct((for(i <- ci * k until (ci + 1) * k; j <- cj * k until (cj + 1) * k)
      yield intConst(s"${i},${j}")).toList))
    val (sol, z) = solve(latinSquareConstraints(n, constr) && cst, str)
    val res = toInt(sol).map(s => Matrix(s.toIndexedSeq, n, n))
    z.delete()
    res

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

  def nQueensCompletion(n: Int, constr: Iterable[(Int, Int)]): Option[Set[(Int, Int)]] =
    val str: Seq[String] = for(i <- 0 until n; j <- 0 until n) yield s"${i},${j}"
    val cst: Z3Type = constr.map((i, j) => intConst(s"${i},${j}")).toList === 1
    val (sol, z) = solve(nQueensConstraints(n) && cst, str)
    val res = toInt(sol).map(_.zipWithIndex.filter((cs, idx) => cs > 0).map((cs, idx) => (idx / n, idx % n)).toSet)
    z.delete()
    res

  def blockedNQueens(n: Int, constr: Iterable[(Int, Int)]): Option[Set[(Int, Int)]] =
    val str: Seq[String] = for(i <- 0 until n; j <- 0 until n) yield s"${i},${j}"
    val cst: Z3Type = constr.map((i, j) => intConst(s"${i},${j}")).toList === 0
    val (sol, z) = solve(nQueensConstraints(n) && cst, str)
    val res = toInt(sol).map(_.zipWithIndex.filter((cs, idx) => cs > 0).map((cs, idx) => (idx / n, idx % n)).toSet)
    z.delete()
    res
}