package satapps

import Z3.{*, given}
import scala.annotation.targetName
import Extensions.*

class Matrix[T](private val s: Seq[T], val r: Int, val c: Int) extends Iterable[T]{
  require(s.size == r * c)

  protected val arr: IndexedSeq[T] = s.toIndexedSeq
  val shape: (Int, Int) = (r, c)

  def unravel: IndexedSeq[T] = arr
  def apply(i: Int, j: Int): T = arr(i * c + j)
  def updated(i: Int, j: Int, v: T): Matrix[T] = Matrix(arr.updated(i * c + j, v), r, c)
  override def iterator = arr.iterator
  override def toString(): String = (for(i <- 0 until r) yield (for(j <- 0 until c) yield apply(i, j).toString ++ " ").reduce(_ ++ _) ++ "\n").reduce(_ ++ _)

  override def equals (m: Any): Boolean =
    m match{
      case m1: Matrix[_] => (for(i <- 0 until r; j <- 0 until c) yield m1(i, j) == apply(i, j)).reduce(_ && _)
      case _ => false
    }

  def hConcatenate(m: Matrix[T]): Matrix[T] = 
    require(m.r == r)
    Matrix(for(i <- 0 until (m.c + c) * r) yield 
      if(i % (m.c + c) < c) this(i / (m.c + c), i % (m.c + c)) else m(i / (m.c + c), (i % (m.c + c)) - c), r, c + m.c)
  

  def vConcatenate(m: Matrix[T]): Matrix[T] = 
    require(m.c == c)
    Matrix(for(i <- 0 until (m.r + r) * c) yield if(i / c < r) this(i / c, i % c) else m(i / c - r, i % c), r + m.r, c)
  
  }

object BooleanMatricesOps {

  given Conversion[Matrix[Boolean], Matrix[Int]] with
    def apply(id: Matrix[Boolean]) = Matrix[Int](id.unravel.map(if _ then 1 else 0), id.r, id.c)

}

object Mat {
  def falses(r: Int, c: Int): Matrix[Boolean] = Matrix[Boolean]((0 until r * c).map(_ => false).toSeq, r, c)
  def zeros(r: Int, c: Int): Matrix[Int] = Matrix[Int]((0 until r * c).map(_ => 0).toSeq, r, c)

  def id(n: Int) = Matrix[Boolean](for(i <- 0 until n; j <- 0 until n) yield if (i == j) true else false, n, n)
  def ones(r: Int, c: Int) = Matrix[Boolean]((0 until r * c).map(_ => true).toSeq, r, c)


  def fromBlock[T](ul: Matrix[T], ur: Matrix[T], ll: Matrix[T], lr: Matrix[T]) : Matrix[T] = 
    ul.hConcatenate(ur).vConcatenate(ll.hConcatenate(lr))


  private def latinSquareConstraints(n: Int, constr: Iterable[(Int, Int, Int)]): Z3Type =
    val str: Seq[String] = for(i <- 0 until n; j <- 0 until n) yield s"${i},${j}"
    val vars: Seq[Z3Type] = intConst(str)

    val cst1: Z3Type = vars >= 0 && vars <= n
    val cst2: Z3Type = andAll(constr.map((i, j, v) => intConst(s"${i},${j}") === v).toList)
    val cst3: Z3Type = andAll(for(i <- 0 until n) yield distinct(for(j <- 0 until n) yield intConst(s"${i},${j}")))
    val cst4: Z3Type = andAll(for(j <- 0 until n) yield distinct(for(i <- 0 until n) yield intConst(s"${i},${j}")))
    andAll(List(cst1, cst2, cst3, cst4))

  def latinSquare(n: Int, constr: Iterable[(Int, Int, Int)]): Option[Matrix[Int]] = 
    val str: Seq[String] = for(i <- 0 until n; j <- 0 until n) yield s"${i},${j}"
    val (sol, z) = solve(latinSquareConstraints(n, constr), str)
    val res = toInt(sol).map(Matrix(_, n, n))
    z.delete()
    res
  
  def sudoku(k: Int, constr: Iterable[(Int, Int, Int)]): Option[Matrix[Int]] = 
    val n = k * k
    val str: Seq[String] = for(i <- 0 until n; j <- 0 until n) yield s"${i},${j}"
    val cst: Z3Type = andAll(for(ci <- 0 until k; cj <- 0 until k)
      yield distinct((for(i <- ci * k until (ci + 1) * k; j <- cj * k until (cj + 1) * k)
      yield intConst(s"${i},${j}")).toList))
    val (sol, z) = solve(latinSquareConstraints(n, constr) && cst, str)
    val res = toInt(sol).map(Matrix(_, n, n))
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