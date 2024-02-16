package satapps

import scala.annotation.targetName
import Extensions.*
import java.util.ArrayList

/** Two dimensional immutable matrix.
  *
  * The name of the methods and their behavior aim to be as similar as possible
  * to [Numpy](https://numpy.org). Note however that regular Scala syntax is
  * used for indexing and all the operations are stateless.
  *
  * @tparam A
  *   the entry type of the matrix. This type is covariant, meaning that if `A
  *   <: B` then `Matrix[A] <: Matrix[B]`.
  *
  * @constructor
  *   Takes the flattened array of the matrix, i.e. a sequence of all entries
  *   rows by rows, the number of rows and the number of columns. The number of
  *   rows and columns must be positive and the shape of the matrix has to be
  *   compatible with the number of entries: `rows * columns == flatten.size`.
  * 
  *   @todo
  *     - astype
  *     - real
  *     - imaginary
  */
class Matrix[+A](
    val flatten: IndexedSeq[A],
    val rows: Int,
    val columns: Int
) {
  require(
    flatten.size == rows * columns,
    s"The dimension of the matrix must be compatible with the number of entries: entries ${flatten.size}, shape ${rows} x ${columns}."
  )
  require(rows > 0, s"The number of rows must be positive: current ${rows}.")
  require(
    columns > 0,
    s"The number of columns must be positive: current ${columns}."
  ) 

  /**
    *  ## Layout
    * 
    * The following attributes contain information about the layout of the matrix.
    */

    /** Pair of matrix dimensions. */
    def shape: (Int, Int) = (rows, columns)

    /** Number if dimensions of the matrix, .i.e. 2. */
    def ndim: Int = 2

    /** Returns the number of entries of this matrix
      * @note
      *   has a O(1) complexity.
      */
    def size: Int = rows * columns

  /**
    * ## Array conversion
    */

  /** Converts this matrix to a list containing its entries. */
  def toList: List[A] = flatten.toList

  /** Converts this matrix into a string. */
  override def toString(): String =
    (for i <- 0 until flatten.size
    yield s"${flatten(i)} " + (if (i + 1) % columns == 0 then "\n"
                               else "")).flatten.toString()

  /**
    * Fills this matrix with a value
    * 
    * @param v
    *  all entries of the matrix will be assigned this value.
    */
  def fill[B](v: B): Matrix[B] = Matrix.fill(rows, columns)(v) 

  /**
    * ## Shape manipulation
    * 
    * For reshape and resize, the single pair argument may be replaced with 2 integers .
    */

  /** Gives a new shape to this matrix without changing its entries. The new
    * shape should be compatible with the original shape. One shape dimension
    * can be -1. In this case, the value is inferred from the number of entries
    * in the matrix and the remaining dimension. Returns the original matrix if
    * both dimensions are -1.
    *
    * @param newRows
    *   number of rows in the new matrix.
    * @param newCol
    *   number of columns in the new matrix.
    *
    * @throws IllegalArgumentException
    *   If `newRows` or `newCol` are not positive or set to -1, and if the new
    *   shape is not compatible with the number of entries of this matrix.
    */
  def reshape(newRows: Int, newCol: Int): Matrix[A] =
    val numberEntries: Int = flatten.size
    if newRows > numberEntries then
      throw IllegalArgumentException(
        s"The new matrix cannot have more rows than entries in the original one: current ${newRows}, expected less or equal than ${numberEntries}."
      )
    else if newCol > numberEntries then
      throw IllegalArgumentException(
        s"The new matrix cannot have more columns than entries in the original one: current ${newRows}, expected less or equal than ${numberEntries}."
      )
    else if newRows != -1 && newCol != -1 && newRows * newCol != numberEntries
    then
      throw IllegalArgumentException(
        s"The new shape of the matrix must be compatible with the original one: current ${newRows} x ${newCol} = ${newRows * newCol}, original shape ${rows} x ${columns} = ${numberEntries}."
      )
    else if newRows < -1 then
      throw IllegalArgumentException(
        s"The number of rows of the new matrix must be positive or -1: current ${newRows}."
      )
    else if newCol < -1 then
      throw IllegalArgumentException(
        s"The number of rows of the new matrix must be positive or -1: current ${newCol}."
      )
    else if newRows == -1 then
      if newCol == -1 then this
      else Matrix(flatten, numberEntries / newCol, newCol)
    else if newCol == -1 then Matrix(flatten, newRows, numberEntries / newRows)
    else Matrix(flatten, newRows, newCol)


  /** Change shape and size of this matrix.
    *
    * @param newRows
    *   rows of the resized matrix.
    * @param newCol
    *   columns of the resized matrix.
    */
  def resize(newRows: Int, newCol: Int): Matrix[A] =
    if newRows < 0 then
      throw IllegalArgumentException(
        s"The number of rows of the new matrix must be positive: current ${newRows}."
      )
    else if newCol < 0 then
      throw IllegalArgumentException(
        s"The number of rows of the new matrix must be positive: current ${newCol}."
      )
    Matrix(flatten.take(newRows * newCol), newRows, newCol)

  /** Overload of [[this.resize]], taking a tuple as parameter instead of two
    * integers.
    */
  def resize(newShape: (Int, Int)): Matrix[A] = resize(newShape._1, newShape._2)

  /** Returns the transpose of this matrix. */
  def transpose: Matrix[A] =
    val emptyColumn: IndexedSeq[List[A]] =
      IndexedSeq.fill(columns)(List.empty[A])
    // Since `Lists` are used to add elements, using foldRight
    // instead of foldLeft increases performances.
    Matrix(
      flatten
        .grouped(columns)
        .foldRight(emptyColumn)((acc, col) =>
          acc.zip(col).map((h, t) => (h :: t))
        )
        .flatten
        .toIndexedSeq,
      columns,
      rows
    )

  /** Alias of [[this.transpose]] */
  def T: Matrix[A] = transpose

  /** Alias of [[this.transpose]] */
  def swapaxes: Matrix[A] = transpose

  /** Alias of [[this.flatten]] */
  def ravel: IndexedSeq[A] = flatten

  /** Remove an axis of length one from this matrix.
    *
    * @param axis
    *   the axis to be removed. If set to [[Axis.None]], the axis is
    *   automatically infered.
    *
    * @throws IllegalStateException
    *   if the shape entry of the selected axis is greater than one.
    */
  def squeeze(axis: Axis): IndexedSeq[A] =
    axis match
      case Axis.None =>
        if rows > 1 && columns > 1 then
          throw IllegalStateException(
            s"The matrix must be a vector: current shape ${shape}"
          )
        else flatten
      case Axis.Vertical =>
        if rows > 1 then
          throw IllegalStateException(
            s"The matrix must be a row vector: current shape ${shape}"
          )
        else flatten
      case Axis.Horizontal =>
        if columns > 1 then
          throw IllegalStateException(
            s"The matrix must be a column vector: current shape ${shape}"
          )
        else flatten

  /** Alias for [[this.item]].
    *
    * @note
    *   Exists in both curried and uncurried notation.
    */
  def apply(i: Int, j: Int): A = item((i, j))

  @targetName("CurryApply")
  /** Curry version of [[this.apply]] */
  def apply(i: Int)(j: Int): A = this.apply(i, j)

  /** Optional entry at given index.
    *
    * Indices start at 0. Returns [[None]] if the index is out of bounds, and
    * returns the entry wrapped in an [[Option]] otherwise.
    *
    * @param i
    *   the row index.
    * @param j
    *   the column index.
    *
    * @see
    *   [[this.apply]] for the equivalent function without functional error
    *   handling.
    */
  def get(i: Int, j: Int): Option[A] =
    if i < 0 || i >= rows || j < 0 || j >= columns then None
    else Some(apply(i, j))

  /** The entry at given index.
    *
    * Indices start at 0.
    *
    * @param ind
    *   the row and column index.
    *
    * @throws ArrayIndexOutOfBoundsException
    *   if `ind._1` or `ind._2` are negative or above their respective bounds.
    *
    * @see
    *   [[this.get]] for the equivalent function with functional error handling.
    */
  def item(ind: (Int, Int)): A =
    val i = ind._1
    val j = ind._2
    if i < 0 || i >= rows then
      throw ArrayIndexOutOfBoundsException(
        s"The row index is out of bounds: current ${i}, expected between 0 and ${rows}."
      )
    else if j < 0 || j >= columns then
      throw ArrayIndexOutOfBoundsException(
        s"The column index is out of bounds: current ${j}, expected between 0 and ${columns}."
      )
    else item(i * columns + j)

  /** The entry at given index.
    *
    * Index starts at 0.
    *
    * @param ind
    *   the index of the entry. It is row wise and passes to the next row if it
    *   overflows.
    *
    * @throws ArrayIndexOutOfBoundsException
    *   if `ind` is greater or equal than the number of entries.
    */
  def item(ind: Int): A =
    if ind > flatten.size then
      throw ArrayIndexOutOfBoundsException(
        s"The given index is out of bounds: current ${ind}, expected between 0 and ${size}"
      )
    else flatten(ind)

  /** Alias for [[this.itemset]] */
  def updated[S >: A](i: Int, j: Int, v: S): Matrix[S] =
    itemset((i, j), v)

  /** Returns this matrix with one of the entries replaced by another value.
    *
    * Indices start at 0.
    *
    * @param ind
    *   the row and column index of the entry.
    * @param v
    *   the new value.
    *
    * @throws ArrayIndexOutOfBoundsException
    *   if `ind._1` or `ind._2` are negative or above their respective bounds.
    */
  def itemset[S >: A](ind: (Int, Int), v: S): Matrix[S] =
    val i = ind._1
    val j = ind._2
    if i < 0 || i >= rows then
      throw ArrayIndexOutOfBoundsException(
        s"The row index is out of bounds: current ${i}, expected between 0 and ${rows}."
      )
    else if j < 0 || j >= columns then
      throw ArrayIndexOutOfBoundsException(
        s"The column index is out of bounds: current ${j}, expected between 0 and ${columns}."
      )
    else itemset(i * columns + j, v)

  /** Returns this matrix with one of the entries replaced by another value.
    *
    * Index starts at 0.
    *
    * @param ind
    *   the index of the entry that should be replaced. It is row wise and
    *   passes to the next row if it overflows.
    * @param v
    *   the new value.
    *
    * @throws ArrayIndexOutOfBoundsException
    *   if `ind` is greater or equal than the number of entries.
    */
  def itemset[S >: A](ind: Int, v: S): Matrix[S] =
    if ind > flatten.size then
      throw ArrayIndexOutOfBoundsException(
        s"The given index is out of bounds: current ${ind}, expected between 0 and ${size}"
      )
    else Matrix(flatten.updated(ind, v), rows, columns)

  /** Returns this matrix with a list entries replaced by other values.
    *
    * Indices starts at 0.
    *
    * @param ind
    *   the indices of the entries that should be replaced. They are row wise
    *   and pass to the next row if they overflows.
    * @param v
    *   the list of new values.
    *
    * @throws IllegalArgumentException
    *   if the number of indices is different from the number of values to be
    *   replaced.
    */
  def put[S >: A](ind: Seq[Int], v: Seq[S]): Matrix[S] =
    ind.zip(v).foldLeft(this)((acc: Matrix[S], p) => acc.itemset(p._1, p._2))



  /** An iterator for this matrix that outputs its entries row by row. */
  def flat: Iterator[A] = flatten.iterator

  /** Alias for [[this.flat]]. */
  def iterator: Iterator[A] = flat



  /** Returns whether this matrix is identical to another one
    *
    * @param m
    *   the other matrix to be compared.
    */
  override def equals(m: Any): Boolean =
    m match {
      case m1: Matrix[_] =>
        this.rows == m1.rows && this.columns == m1.columns && this.flatten == m1.flatten
      case _ => false
    }




  /** Stacks matrices in sequence horizontally.
    *
    * @param ms
    *   the sequence of matrices to concatenate with this matrix.
    *
    * @throws IllegalArgumentException
    *   if not all the matrices have the same number of rows.
    */
  def hstack[B >: A](ms: Matrix[B]*): Matrix[B] =
    try this.T.vstack((ms.map(_.T))*).T
    catch
      case e: IllegalArgumentException =>
        throw IllegalArgumentException(
          s"The shapes of the matrices must be compatible: this.rows = ${rows}."
        )
      case _ =>
        throw UnknownError()

  /** Alias for [[this.hstack]] */
  def ++[B >: A](m: Matrix[B]): Matrix[B] = vstack(m)

  /** Stacks matrices in sequence vertically.
    *
    * @param ms
    *   the sequence of matrices to concatenate with this matrix.
    *
    * @throws IllegalArgumentException
    *   if not all the matrices have the same number of columns.
    */
  def vstack[S >: A](ms: Matrix[S]*): Matrix[S] =
    ms.foldLeft(this)((acc: Matrix[S], m) =>
      if m.columns != acc.columns then
        throw IllegalArgumentException(
          s"The shapes of the matrices must be compatible: this.columns = ${columns}."
        )
      else Matrix(acc.flatten ++ m.flatten, acc.rows + m.rows, acc.columns)
    )

  /** Concatenate matrices in sequence along an axis
    *
    * @param ms
    *   the sequence of matrices to concatenate with this matrix.
    * @param axis
    *   the axis along which the matrices are concatenated. 0 or
    *   [[Axis.Vertical]] stands for the vertical axis (row wise concatenation)
    *   while 1 or [[Axis.Horizontal]] stands for the horizointal axis (column
    *   wise concatenation). [[Axis.None]] cannot be used as an argument here.
    *
    * @throws IllegalArgumentException
    *   if `axis` is different from 0 or 1
    */
  def concatenate[S >: A](ms: Seq[Matrix[S]], axis: Axis = 0): Matrix[S] =
    axis match
      case Axis.Vertical   => vstack(ms*)
      case Axis.Horizontal => hstack(ms*)
      case _ =>
        throw IllegalArgumentException(
          s"Axis should be 0 or 1, current ${axis}"
        )

  



  /** 
   * Return the maximum entry of this matrix. 
   * 
   * @param ord
   *  ordering used to compute the maximum element.
   */
  def max[B >: A](implicit ord: Ordering[B]): B = flatten.max

  /** 
   * Return the maximum entry of this matrix along an axis. 
   * 
   * @param axis
   *  axis along which maximum elements are computed.
   * 
   * @param ord
   *  ordering used to compute the maximum element.
   */
  def max[B >: A](axis: Axis)(implicit ord: Ordering[B]): IndexedSeq[B] = Matrix.applyAlongAxis[B, B](_.max, axis, this)

  /** 
   * Return the minimum entry of this matrix. 
   * 
   * @param ord
   *  ordering used to compute the minimum element.
   */
  def min[B >: A](implicit ord: Ordering[B]): B = flatten.min

 /** 
   * Return the minimum entry of this matrix along an axis. 
   * 
   * @param axis
   *  axis along which minimum elements are computed.
   * 
   * @param ord
   *  ordering used to compute the minimum element.
   */
  def min[B >: A](axis: Axis)(implicit ord: Ordering[B]): IndexedSeq[B] = Matrix.applyAlongAxis[B, B](_.min, axis, this)

  /** Returns the specified diagonal of this matrix.
    *
    * @param offset
    *   Offset of the diagonal from the main diagonal. Can be positive or
    *   negative. Defaults to main diagonal (0).
    */
  def diagonal(offset: Int = 0): IndexedSeq[A] =
    for
      i <- 0 until Math.min(rows, columns)
      if 0 <= i + offset && i + offset <= columns
    yield apply(i, i + offset)



  /** Builds a new matrix by applying a function to all entries of this matrix.
    *
    * @param f
    *   the function to apply to each element
    */
  def map[B](f: A => B): Matrix[B] = new Matrix(flatten.map(f), rows, columns)


}

type Axis = Int

/** Axes of a matrix. In order to be compatible with Numpy notation, axes are
  * integers. 0 denotes the vertical axis while 1 the horizontal one. When no
  * axis is provided -1 is used.
  */
object Axis {
  val None: Axis = -1
  val Vertical: Axis = 0
  val Horizontal: Axis = 1
}

/** This object provides a set of operations to creates matrices. */
object Matrix {

  /** Creates a matrix with the specified rows.
    *
    * @param rows
    *   the list of rows of the matrix
    */
  def apply[T](rows: Seq[T]*): Matrix[T] =
    val columns = rows(0).length
    if rows.exists(rows => rows.length != columns) then
      throw IllegalArgumentException("All the rows must be of the same length.")
    else new Matrix[T](rows.flatten.toIndexedSeq, rows.length, columns)

  /** Creates a matrix with the specified entries and shape.
    *
    * @param arr
    *   the entries of the matrix row by row.
    * @param rows
    *   the number of rows in the matrix
    * @param columns
    *   the number of columns in the matrix
    */
  def apply[T](arr: Seq[T], rows: Int, columns: Int): Matrix[T] =
    new Matrix[T](arr.toIndexedSeq, rows, columns)

  /** Creates a matrix with the specified entries and shape.
    *
    * @param arr
    *   the entries of the matrix row by row.
    * @param rows
    *   the number of rows in the matrix
    * @param columns
    *   the number of columns in the matrix
    */
  def fill[T](rows: Int, columns: Int)(t: T) =
    require(rows >= 0 && columns >= 0)
    Matrix[T](IndexedSeq.fill(rows * columns)(t), rows, columns)

  def eye[A](d: A, o: A)(n: Int) =
    require(n >= 0)
    Matrix[A](
      for (i <- 0 until n; j <- 0 until n) yield if (i == j) d else o,
      n,
      n
    )

  def fromBlock[A](
      ul: Matrix[A],
      ur: Matrix[A],
      ll: Matrix[A],
      lr: Matrix[A]
  ): Matrix[A] =
    ul.hstack(ur).vstack(ll.hstack(lr))

  /** */
  def applyAlongAxis[A, B](
      f: Iterable[A] => B,
      axis: Axis,
      arr: Matrix[A]
  ): IndexedSeq[B] =
    axis match
      case Axis.Horizontal =>
        (for i <- 0 until arr.rows
        yield f(for j <- 0 until arr.columns yield arr(i)(j))).toIndexedSeq
      case Axis.Vertical =>
        (for j <- 0 until arr.columns
        yield f(for i <- 0 until arr.rows yield arr(i)(j))).toIndexedSeq
      case _ =>
        throw IllegalArgumentException(s"Axis must be 0 or 1: curent ${axis}")

}

object BoolMatrix {
  def trues(rows: Int, columns: Int): Matrix[Boolean] =
    require(rows >= 0)
    require(columns >= 0)
    Matrix.fill(rows, columns)(true)
  def falses(rows: Int, columns: Int): Matrix[Boolean] =
    require(rows >= 0)
    require(columns >= 0)
    Matrix.fill(rows, columns)(false)
  def id(n: Int) =
    require(n >= 0)
    Matrix.eye(true, false)(n)

  given Conversion[Matrix[Boolean], Matrix[Int]] with
    def apply(id: Matrix[Boolean]) = id.map(if _ then 1 else 0)
}

object IntMatrix {
  def zeros(rows: Int, columns: Int): Matrix[Int] =
    Matrix.fill(rows, columns)(0)
  def ones(rows: Int, columns: Int) = Matrix.fill(rows, columns)(1)
  def id(n: Int) = Matrix.eye(1, 0)(n)
}
