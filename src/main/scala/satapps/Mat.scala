package satapps

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

object Matrix {
  def uniform[T](t: T)(r: Int, c: Int) = Matrix[T]((0 until r * c).map(_ => t).toSeq, r, c)
  def eye[T](d: T, o: T)(n: Int) = Matrix[T](for(i <- 0 until n; j <- 0 until n) yield if (i == j) d else o, n, n)

  def fromBlock[T](ul: Matrix[T], ur: Matrix[T], ll: Matrix[T], lr: Matrix[T]) : Matrix[T] = 
    ul.hConcatenate(ur).vConcatenate(ll.hConcatenate(lr))
}

object BoolMatrix {
  def trues(r: Int, c: Int): Matrix[Boolean] = Matrix.uniform(false)(r, c)
  def falses(r: Int, c: Int): Matrix[Boolean] = Matrix.uniform(false)(r, c)
  def id(n: Int) = Matrix.eye(true, false)(n)
}

object IntMatrix {
  def zeros(r: Int, c: Int): Matrix[Int] = Matrix.uniform(0)(r, c)
  def ones(r: Int, c: Int) = Matrix.uniform(1)(r, c)
  def id(n: Int) = Matrix.eye(1, 0)(n)
}