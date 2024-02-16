package satapps

import ConstrProg.*
import z3.scala.*
import z3.scala.dsl.BoolConstant
import scala.runtime.ScalaNumberProxy

object Extensions {

  extension (a: Seq[IntConstr])
    def +(b: Seq[IntConstr]): Seq[IntConstr] = a.zip(b).map(_ + _)
    def *(b: Seq[IntConstr]): Seq[IntConstr] = a.zip(b).map(_ * _)
    def -(b: Seq[IntConstr]): Seq[IntConstr] = a.zip(b).map(_ - _)
    def ===(b: Seq[IntConstr]): BoolConstr = And(a.zip(b).map(_ === _): _*)
    def ===(b: IntConstr): BoolConstr = And(a.map(_ === b): _*)
    def <=(b: Seq[IntConstr]): BoolConstr = And(a.zip(b).map(_ <= _): _*)
    def <=(b: IntConstr): BoolConstr = And(a.map(_ <= b): _*)
    def >=(b: Seq[IntConstr]): BoolConstr = And(a.zip(b).map(_ >= _): _*)
    def >=(b: IntConstr): BoolConstr = And(a.map(_ >= b): _*)
    def <(b: Seq[IntConstr]): BoolConstr = And(a.zip(b).map(_ < _): _*)
    def <(b: IntConstr): BoolConstr = And(a.map(_ < b): _*)
    def >(b: Seq[IntConstr]): BoolConstr = And(a.zip(b).map(_ > _): _*)
    def >(b: IntConstr): BoolConstr = And(a.map(_ > b): _*)

  extension (a: Matrix[Boolean])

    /** Tests whether all entries of this matrix evaluate to `true`. */
    def all(): Boolean = a.flatten.forall(b => b)

    /** Tests whether all entries along a given axis evaluates to `true`.
      *
      * @param axis
      *   axis along which a logical `AND` reduction is performed.
      */
    def all(axis: Axis): Seq[Boolean] =
      Matrix.applyAlongAxis[Boolean, Boolean](_.forall(b => b), axis, a)

    /** Tests whether any entry of this matrix evaluate to `true`. */
    def any(): Boolean = a.flatten.exists(b => b)

    /** Tests whether any entry along a given axis evaluates to `true`.
      *
      * @param axis
      *   axis along which a logical `OR` reduction is performed.
      */
    def any(axis: Axis): Seq[Boolean] =
      Matrix.applyAlongAxis[Boolean, Boolean](_.exists(b => b), axis, a)

  //   def ^(m2: Matrix[Boolean]): Matrix[Boolean] =
  //     require(a.shape == m2.shape)
  //     a.zip(m2).map(_^_)
  //   def ||(m2: Matrix[Boolean]): Matrix[Boolean] =
  //     require(a.shape == m2.shape)
  //     a.zip(m2).map(_||_)
  //   def &&(m2: Matrix[Boolean]): Matrix[Boolean] =
  //     require(a.shape == m2.shape)
  //     a.zip(m2).map(_&&_)
  //   def complement : Matrix[Boolean] = Matrix[Boolean](a.flatten.map(!_), a.rows, a.columns)

  // def *(b2: Matrix[Boolean]): Matrix[Boolean] =
  //   require(a.columns == b2.rows)
  //   Matrix[Boolean](
  //     (for(i <- 0 until a.rows; j <- 0 until b2.columns)
  //       yield (for(k <- 0 until a.columns) yield a(i, k) && b2(k, j)).reduce(_ || _)).toIndexedSeq
  //     , a.rows, b2.columns)

  // def pow(n: Int): Matrix[Boolean] =
  //   require(n > 0 && a.rows == a.columns)
  //   n match{
  //     case 1 => a
  //     case _ => *(pow(n - 1))
  //   }

  // def transClos(): Matrix[Boolean] =
  //   require(a.rows == a.columns)
  //   def transPow(bef: Matrix[Boolean], aft: Matrix[Boolean]): Matrix[Boolean] =
  //     if(bef equals aft)
  //       bef
  //     else
  //       transPow(aft, aft || (a * aft))

  //   transPow(a, a || (a * a))

  extension [T](s: Iterable[Set[T]])
    def isPartition(universe: Set[T]): Boolean =
      s.foldLeft((universe, 0))((acc, e) =>
        (acc._1 -- e, acc._2 + e.size)
      ) == (Set(), universe.size)

  extension (s: NumQuery)
    def toInt: IntQuery =
      IntQuery(
        s.map((k, v) =>
          (
            k,
            v match {
              case i: IntNum => i.c
              case _         => throw IllegalStateException()
            }
          )
        ).toMap
      )

  extension (s: IntQuery)
    def filterPositive: IntQuery = s.filterVal(_ > 0)
    def filterIdx: Set[Int] = s.filterPositive.varSet.map(_.toInt)
    def filterPairIdx: Set[(Int, Int)] = s.filterPositive.varSet.map {
      case s"${v1},${v2}" => (v1.toInt, v2.toInt)
    }

}
