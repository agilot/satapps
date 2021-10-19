package satapps
import scala.collection.mutable.ArrayBuffer

trait Matrix[T](private val arr: collection.AbstractSeq[T], val r: Int, val c: Int){
  require(arr.size == r * c)
  def apply(i: Int, j: Int): T = arr(i * c + j)
  def set(i: Int, j: Int, v: T): Matrix[T]
  def iterator() = arr.iterator
  override def toString(): String = (for(i <- 0 until r) yield (for(j <- 0 until c) yield apply(i, j).toString ++ " ").reduce(_ ++ _) ++ "\n").reduce(_ ++ _)
}

trait BinaryMatrix extends Matrix[Boolean]{
  def or(b2: BinaryMatrix): BinaryMatrix
  def xor(b2: BinaryMatrix): BinaryMatrix
  def transClos(): BinaryMatrix
  def mult(m: BinaryMatrix): BinaryMatrix
  def pow(n: Int): BinaryMatrix
  def complement: BinaryMatrix
  override def toString(): String = (for(i <- 0 until r) yield (for(j <- 0 until c) yield (if (apply(i, j)) "1" else "0") ++ " ").reduce(_ ++ _) ++ "\n").reduce(_ ++ _)

}


class MutMatrix[T](private val arr: ArrayBuffer[T], override val r: Int, override val c: Int) extends Matrix[T](arr, r, c){
  override def set(i: Int, j: Int, v: T): MutMatrix[T] =
    arr(i * c + j) = v
    this
  
  def immutable(): ImMatrix[T] =
    ImMatrix(arr.toList, r, c)
}

class BinaryMutMatrix(private val arr: ArrayBuffer[Boolean], override val r: Int, override val c: Int) extends MutMatrix[Boolean](arr, r, c){
  def xor(m2: Matrix[Boolean]) = {
    for (i <- 0 until r; j <- 0 until c){
      set(i, j, apply(i, j) ^ m2(i, j))
    }
    this
  }

  override def immutable() = BinaryImMatrix(arr.toList, r, c)
}

class ImMatrix[T](private val arr: List[T], override val r: Int, override val c: Int) extends Matrix[T](arr, r, c){
  override def set(i: Int, j: Int, v: T): ImMatrix[T] =
    ImMatrix(arr.updated(i * c + j, v), r, c)
}

class BinaryImMatrix(private val arr: List[Boolean], override val r: Int, override val c: Int) extends ImMatrix[Boolean](arr, r, c) with BinaryMatrix{
  override def set(i: Int, j: Int, v: Boolean): BinaryImMatrix = BinaryImMatrix(arr.updated(i * c + j, v), r, c)
  def xor(m2: BinaryMatrix): BinaryImMatrix = BinaryImMatrix(arr.zip(m2.iterator().toList).map(_^_), r, c)
  def or(m2: BinaryMatrix): BinaryImMatrix = BinaryImMatrix(arr.zip(m2.iterator().toList).map(_||_), r, c)
  def complement : BinaryImMatrix = BinaryImMatrix(arr.map(!_), r, c)

  override def equals (m: Any): Boolean = 
    if (m.isInstanceOf[BinaryImMatrix])
      m.asInstanceOf[BinaryImMatrix].arr == arr
    else false

  override def mult(b2: BinaryMatrix): BinaryImMatrix =
    require(c == b2.r)
    BinaryImMatrix(
      (for(i <- 0 until r; j <- 0 until b2.c)
        yield (for(k <- 0 until c) yield apply(i, k) && b2(k, j)).reduce(_ || _)).toList
      , r, b2.c)
    
  override def pow(n: Int): BinaryImMatrix = 
    require(n > 0 && r == c)
    n match{
      case 1 => this
      case _ => mult(pow(n - 1))
    }

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