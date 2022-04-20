package satapps

import scala.annotation.targetName
import Extensions.*

class Matrix[T] private(private val arr: IndexedSeq[T], val rows: Int, val columns: Int) extends Iterable[T]{
  require(arr.size == rows * columns)

  val shape: (Int, Int) = (rows, columns)

  def unravel: IndexedSeq[T] = arr
  def apply(i: Int, j: Int): T = arr(i * columns + j)
  def apply(i: Int): Int => T = (j: Int) => this.apply(i, j)
  def updated(i: Int, j: Int, v: T): Matrix[T] = Matrix(arr.updated(i * columns + j, v), rows, columns)
  override def iterator = arr.iterator
  def nestedIterators = iterator.grouped(columns).map(_.iterator)
  override def toString(): String =
    nestedIterators.map(_.mkString(" ")).mkString("\n")

  override def equals(m: Any): Boolean =
    m match {
      case m1: Matrix[_] => this.rows == m1.rows && this.columns == m1.columns && this.unravel == m1.unravel
      case _ => false
    }

  def hConcatenate(m: Matrix[T]): Matrix[T] = 
    require(m.rows == rows)
    Matrix(
      this.arr.grouped(this.columns)
        .zip(m.arr.grouped(m.columns))
        .flatMap( (l, r) => l ++ r )
        .toIndexedSeq,
      this.rows,
      this.columns + m.columns
    )

  def vConcatenate(m: Matrix[T]): Matrix[T] = 
    require(m.columns == columns)
    Matrix( this.arr ++ m.arr, this.rows + m.rows, this.columns )


  override def map[S](f: T => S): Matrix[S] = {
    new Matrix( arr.map(f), rows, columns )
  }
}

object BooleanMatricesOps {
  given Conversion[Matrix[Boolean], Matrix[Int]] with
    def apply(id: Matrix[Boolean]) = id.map(if _ then 1 else 0)
}

object Matrix {
  def apply[T](rows: Seq[T]*): Matrix[T] = {
    require(rows.length > 0)
    val columns = rows(0).length
    require(rows.forall(rows => rows.length == columns))
    
    new Matrix[T](rows.flatten.toIndexedSeq, rows.length, columns)
  }

  def apply[T](arr: IndexedSeq[T], rows: Int, columns: Int): Matrix[T] = {
    new Matrix[T](arr, rows, columns)
  }

  def fill[T](t: T)(rows: Int, columns: Int) = Matrix[T](IndexedSeq.fill(rows*columns)(t), rows, columns)
  def eye[T](d: T, o: T)(n: Int) = Matrix[T](for(i <- 0 until n; j <- 0 until n) yield if (i == j) d else o, n, n)

  def fromBlock[T](ul: Matrix[T], ur: Matrix[T], ll: Matrix[T], lr: Matrix[T]) : Matrix[T] = 
    ul.hConcatenate(ur).vConcatenate(ll.hConcatenate(lr))
}

object BoolMatrix {
  def trues(rows: Int, columns: Int): Matrix[Boolean] = Matrix.fill(true)(rows, columns)
  def falses(rows: Int, columns: Int): Matrix[Boolean] = Matrix.fill(false)(rows, columns)
  def id(n: Int) = Matrix.eye(true, false)(n)
}

object IntMatrix {
  def zeros(rows: Int, columns: Int): Matrix[Int] = Matrix.fill(0)(rows, columns)
  def ones(rows: Int, columns: Int) = Matrix.fill(1)(rows, columns)
  def id(n: Int) = Matrix.eye(1, 0)(n)
}