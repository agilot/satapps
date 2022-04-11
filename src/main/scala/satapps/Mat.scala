package satapps
import scala.collection.mutable.ArrayBuffer
import scala.collection.{IterableOps, IterableFactory, IterableFactoryDefaults, StrictOptimizedIterableOps}
import scala.collection.mutable.{Builder, ImmutableBuilder}
import scala.collection.mutable

trait Matrix[T] extends Iterable[T]{
  val rows: Int
  val cols: Int
  val shape: (Int, Int) = (rows, cols)
  def apply(i: Int, j: Int): T
  def updated(i: Int, j: Int, v: T): Matrix[T]
  override def toString(): String = (for(i <- 0 until rows) yield (for(j <- 0 until cols) yield apply(i, j).toString ++ " ").reduce(_ ++ _) ++ "\n").reduce(_ ++ _)

  override def equals (m: Any): Boolean =
    m match{
      case m1: Matrix[_] => (for(i <- 0 until rows; j <- 0 until cols) yield m1(i, j) == apply(i, j)).reduce(_ && _)
      case _ => false
    }
  }

trait BinaryMatrix extends Matrix[Boolean]{
  def ||(b2: BinaryMatrix): BinaryMatrix
  def ^(b2: BinaryMatrix): BinaryMatrix
  def transClos(): BinaryMatrix
  def *(m: BinaryMatrix): BinaryMatrix
  def ^(n: Int): BinaryMatrix =
    require(n > 0 && rows == cols)
    n match{
      case 1 => this
      case _ => *(^(n - 1))
    }
  def complement: BinaryMatrix
  override def toString(): String = (for(i <- 0 until rows) yield (for(j <- 0 until cols) yield (if (apply(i, j)) "1" else "0") ++ " ").reduce(_ ++ _) ++ "\n").reduce(_ ++ _)
}

abstract class SeqMatrix[T](private val arr: scala.collection.Seq[T], private val r: Int, private val c: Int) extends Matrix[T]{
    require(arr.size == r * c)

    override val rows = r
    override val cols = c

    override def apply(i: Int, j: Int): T = arr(i * c + j)
    override def iterator = arr.iterator


}

class MutMatrix[T](private val arr: mutable.Seq[T], private val r: Int, private val c: Int) extends SeqMatrix[T](arr, r, c){

  override def updated(i: Int, j: Int, v: T): MutMatrix[T] =
    update(i, j, v)
    this
  
  def update(i: Int, j: Int, v: T): Unit = arr(i * c + j) = v
}

class BinaryMutMatrix(private val arr: mutable.Seq[Boolean], private val r: Int, private val c: Int) extends MutMatrix[Boolean](arr, r, c) with BinaryMatrix{
  override def updated(i: Int, j: Int, v: Boolean): BinaryMutMatrix =
    update(i, j, v)
    this
  
  def copy: BinaryMutMatrix =
    BinaryMutMatrix(arr, rows, cols)
  
  override def ^(m2: BinaryMatrix): BinaryMutMatrix = 
    for(i <- 0 until rows; j <- 0 until cols){
      this(i, j) = m2(i, j) ^ this(i, j) 
    }
    this
  override def ||(m2: BinaryMatrix): BinaryMutMatrix = 
    for(i <- 0 until rows; j <- 0 until cols){
        this(i, j) = m2(i, j) || this(i, j) 
    }
    this
  override def complement : BinaryMutMatrix = 
    for(i <- 0 until rows; j <- 0 until cols){
        this(i, j) = !this(i, j) 
    }
    this

  override def *(b2: BinaryMatrix): BinaryMutMatrix =
    require(c == b2.rows)
    var newArr = arr.empty
    for(i <- 0 until r; j <- 0 until b2.cols){
      newArr :+ false
    }
    var mat = BinaryMutMatrix(newArr, r, b2.cols)
    for(i <- 0 until rows; j <- 0 until b2.cols; k <- 0 until cols){
      mat(i, j) = mat(i, j) || (mat(i, k) && b2(k, j))
    }
    mat

  override def transClos(): BinaryMatrix = 
    require(r == c)
    var bef = this.copy
    var aft = this || (this * this)
    while(bef != aft){
      val temp = aft.copy
      aft = aft || (this * aft)
      bef = temp
    }
    bef
}

class ImMatrix[T](private val arr: Seq[T], private val r: Int, private val c: Int) extends SeqMatrix[T](arr, r, c){
  override def updated(i: Int, j: Int, v: T): ImMatrix[T] =
    ImMatrix(arr.updated(i * c + j, v), r, c)
}

class BinaryImMatrix(private val arr: Seq[Boolean], private val r: Int, private val c: Int) extends ImMatrix[Boolean](arr, r, c) with BinaryMatrix{

  override def updated(i: Int, j: Int, v: Boolean): BinaryImMatrix =
    BinaryImMatrix(arr.updated(i * c + j, v), r, c)
  
  override def ^(m2: BinaryMatrix): BinaryImMatrix = BinaryImMatrix(arr.zip(m2.iterator.toList).map(_^_), r, c)
  override def ||(m2: BinaryMatrix): BinaryImMatrix = BinaryImMatrix(arr.zip(m2.iterator.toList).map(_||_), r, c)
  override def complement : BinaryImMatrix = BinaryImMatrix(arr.map(!_), r, c)

  override def *(b2: BinaryMatrix): BinaryImMatrix =
    require(c == b2.rows)
    BinaryImMatrix(
      (for(i <- 0 until r; j <- 0 until b2.cols)
        yield (for(k <- 0 until c) yield apply(i, k) && b2(k, j)).reduce(_ || _)).toList
      , r, b2.cols)

  override def transClos(): BinaryImMatrix = 
    require(r == c)
    def transPow(bef: BinaryImMatrix, aft: BinaryImMatrix): BinaryImMatrix =
      if(bef equals aft)
        bef
      else 
        transPow(aft, aft || (this * aft))
    
    transPow(this, this || (this * this))
    
}

object Mat {
  def imZeros(r: Int, c: Int) = BinaryImMatrix((0 until r * c).map(_ => false).toList, r, c)
  def imId(n: Int) = BinaryImMatrix(for(i <- 0 until n; j <- 0 until n) yield if (i == j) true else false, n, n)

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
    val res = toInt(sol).map(ImMatrix(_, n, n))
    z.delete()
    res
  
  def sudoku(k: Int, constr: Iterable[(Int, Int, Int)]): Option[Matrix[Int]] = 
    val n = k * k
    val str: Seq[String] = for(i <- 0 until n; j <- 0 until n) yield s"${i},${j}"
    val cst: Z3Type = andAll(for(ci <- 0 until k; cj <- 0 until k)
      yield distinct((for(i <- ci * k until (ci + 1) * k; j <- cj * k until (cj + 1) * k)
      yield intConst(s"${i},${j}")).toList))
    val (sol, z) = solve(latinSquareConstraints(n, constr) && cst, str)
    val res = toInt(sol).map(ImMatrix(_, n, n))
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