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
  def or(b2: BinaryMatrix): BinaryMatrix
  def xor(b2: BinaryMatrix): BinaryMatrix
  def transClos(): BinaryMatrix
  def mult(m: BinaryMatrix): BinaryMatrix
  def pow(n: Int): BinaryMatrix =
    require(n > 0 && rows == cols)
    n match{
      case 1 => this
      case _ => mult(pow(n - 1))
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
  
  override def xor(m2: BinaryMatrix): BinaryMutMatrix = 
    for(i <- 0 until rows; j <- 0 until cols){
      this(i, j) = m2(i, j) ^ this(i, j) 
    }
    this
  override def or(m2: BinaryMatrix): BinaryMutMatrix = 
    for(i <- 0 until rows; j <- 0 until cols){
        this(i, j) = m2(i, j) || this(i, j) 
    }
    this
  override def complement : BinaryMutMatrix = 
    for(i <- 0 until rows; j <- 0 until cols){
        this(i, j) = !this(i, j) 
    }
    this

  override def mult(b2: BinaryMatrix): BinaryMutMatrix =
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
    var aft = or(mult(this))
    while(bef != aft){
      val temp = aft.copy
      aft = aft.or(mult(aft))
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
  
  override def xor(m2: BinaryMatrix): BinaryImMatrix = BinaryImMatrix(arr.zip(m2.iterator.toList).map(_^_), r, c)
  override def or(m2: BinaryMatrix): BinaryImMatrix = BinaryImMatrix(arr.zip(m2.iterator.toList).map(_||_), r, c)
  override def complement : BinaryImMatrix = BinaryImMatrix(arr.map(!_), r, c)

  override def mult(b2: BinaryMatrix): BinaryImMatrix =
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
        transPow(aft, aft.or(mult(aft)))
    
    transPow(this, or(mult(this)))
    
}

object Mat {
  def imZeros(r: Int, c: Int) = BinaryImMatrix((0 until r * c).map(_ => false).toList, r, c)
}