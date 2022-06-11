package satapps.problems

import satapps.ConstrProg.{*, given}
import satapps.BooleanMatricesOps.{*, given}
import scala.collection.immutable.ArraySeq
import satapps.Extensions.*
import z3.scala.*
import javax.swing.SpringLayout.Constraints

trait BasicProblem[A, R]{
  def search(args: A): Option[R]
  def decide(args: A): Boolean
  def enumerate(args: A): Set[R]
  def verify(args: A, sol: R): Boolean
}

trait BasicBiProblem[A, B, R] extends BasicProblem[(A, B), R]{
  override def search(args: (A, B)): Option[R] = search(args._1, args._2)
  override def decide(args: (A, B)): Boolean = decide(args._1, args._2)
  override def enumerate(args: (A, B)): Set[R] = enumerate(args._1, args._2)
  override def verify(args: (A, B), sol: R) = verify(args._1, args._2, sol)
  def search(args1: A, args2: B): Option[R]
  def decide(args1: A, args2: B): Boolean
  def enumerate(args1: A, args2: B): Set[R]
  def verify(args1: A, args2: B, sol: R): Boolean
}

trait BasicTriProblem[A, B, C, R] extends BasicBiProblem[(A, B), C, R]{
  override def search(args1: (A, B), args2: C): Option[R] = search(args1._1, args1._2, args2)
  override def decide(args1: (A, B), args2: C): Boolean = decide(args1._1, args1._2, args2)
  override def enumerate(args1: (A, B), args2: C): Set[R] = enumerate(args1._1, args1._2, args2)
  override def verify(args1: (A, B), args2: C, sol: R) = verify(args1._1, args1._2, args2, sol)
  def search(args1: A, args2: B, args3: C): Option[R]
  def decide(args1: A, args2: B, args3: C): Boolean
  def enumerate(args1: A, args2: B, args3: C): Set[R]
  def verify(args1: A, args2: B, args3: C, sol: R): Boolean
}

trait BasicQuadriProblem[A, B, C, D, R] extends BasicTriProblem[(A, B), C, D, R]{
  override def search(args1: (A, B), args2: C, args3: D): Option[R] = search(args1._1, args1._2, args2, args3)
  override def decide(args1: (A, B), args2: C, args3: D): Boolean = decide(args1._1, args1._2, args2, args3)
  override def enumerate(args1: (A, B), args2: C, args3: D): Set[R] = enumerate(args1._1, args1._2, args2, args3)
  override def verify(args1: (A, B), args2: C, args3: D, sol: R): Boolean = verify(args1._1, args1._2, args2, args3, sol)
  def search(args1: A, args2: B, args3: C, args4: D): Option[R]
  def decide(args1: A, args2: B, args3: C, args4: D): Boolean
  def enumerate(args1: A, args2: B, args3: C, args4: D): Set[R]
  def verify(args1: A, args2: B, args3: C, args4: D, sol: R): Boolean
}

trait Problem[A, R] extends BasicProblem[A, R]{
  protected def constraints(args: A): BoolConstr
  protected def solution(args: A): (Option[NumQuery], () => Unit) = 
    val cstr = constraints(args)
    cstr.solve

  protected def convert(args: A, sol: NumQuery): R

  def search(args: A): Option[R] =
    val (sol, delete) = solution(args)
    val res = sol.map(convert(args, _))
    delete()
    res
  def decide(args: A): Boolean = 
    val (sol, delete) = solution(args)
    val res = sol.isDefined
    delete()
    res
  def enumerate(args: A): Set[R] =
    val firstCstr: BoolConstr = constraints(args)

    def newCst(sol: NumQuery): BoolConstr =
      Or(sol.map((k, v) => v match{
        case i : IntNum => IntVar(k) !== i
        case b : BoolNum => BoolVar(k) !== b
        case _ => throw IllegalStateException("Non exhaustive match")
      }).toList)

    def rec(cstr: BoolConstr): Set[R] =
      cstr.solve match{
        case(None, delete) => 
          delete()
          Set()
        case(Some(s), delete) =>
          val res = convert(args, s)
          delete()
          rec(cstr && newCst(s)) + res
      }
    rec(firstCstr)
}

trait BiProblem[A, B, R] extends Problem[(A, B), R] with BasicBiProblem[A, B, R]{

  protected def constraints(args1: A, args2: B): BoolConstr
  protected def convert(args1: A, args2: B, sol: NumQuery): R
  def verify(args1: A, args2: B, sol: R): Boolean
  override protected def constraints(args: (A, B)): BoolConstr = constraints(args._1, args._2)
  override protected def convert(args: (A, B), sol: NumQuery): R = convert(args._1, args._2, sol)
  override def verify(args: (A, B), sol: R) = verify(args._1, args._2, sol)


  override def search(args1: A, args2: B): Option[R] = super[Problem].search((args1, args2))
  override def decide(args1: A, args2: B): Boolean = super[Problem].decide((args1, args2))
  override def enumerate(args1: A, args2: B): Set[R] = super[Problem].enumerate((args1, args2))
}

trait TriProblem[A, B, C, R] extends BiProblem[(A, B), C, R] with BasicTriProblem[A, B, C, R]{

  protected def constraints(args1: A, args2: B, args3: C): BoolConstr
  protected def convert(args1: A, args2: B, args3: C, sol: NumQuery): R
  def verify(args1: A, args2: B, args3: C, sol: R): Boolean
  override protected def constraints(args1: (A, B), args2: C): BoolConstr = constraints(args1._1, args1._2, args2)
  override protected def convert(args1: (A, B), args2: C, sol: NumQuery): R = convert(args1._1, args1._2, args2, sol)
  override def verify(args1: (A, B), args2: C, sol: R) = verify(args1._1, args1._2, args2, sol)


  override def search(args1: A, args2: B, args3: C): Option[R] = super[BiProblem].search((args1, args2), args3)
  override def decide(args1: A, args2: B, args3: C): Boolean = super[BiProblem].decide((args1, args2), args3)
  override def enumerate(args1: A, args2: B, args3: C): Set[R] = super[BiProblem].enumerate((args1, args2), args3)
}

trait QuadriProblem[A, B, C, D, R] extends TriProblem[(A, B), C, D, R] with BasicQuadriProblem[A, B, C, D, R]{

  protected def constraints(args1: A, args2: B, args3: C, args4: D): BoolConstr
  protected def convert(args1: A, args2: B, args3: C, args4: D, sol: NumQuery): R
  def verify(args1: A, args2: B, args3: C, args4: D, sol: R): Boolean

  override protected def constraints(args1: (A, B), args2: C, args3: D): BoolConstr = constraints(args1._1, args1._2, args2, args3)
  override protected def convert(args1: (A, B), args2: C, args3: D, sol: NumQuery): R = convert(args1._1, args1._2, args2, args3, sol)
  override def verify(args1: (A, B), args2: C, args3: D, sol: R): Boolean = verify(args1._1, args1._2, args2, args3, sol)

  override def search(args1: A, args2: B, args3: C, args4: D): Option[R] = super[TriProblem].search((args1, args2), args3, args4)
  override def decide(args1: A, args2: B, args3: C, args4: D): Boolean = super[TriProblem].decide((args1, args2), args3, args4)
  override def enumerate(args1: A, args2: B, args3: C, args4: D): Set[R] = super[TriProblem].enumerate((args1, args2), args3, args4)

}

trait BasicOptProblem[A, T, R] extends BasicBiProblem[A, T, R]{
  protected def opt(cmp: (T, T) => Boolean, succ: T => T)(args1: A, start: T, end: T): Option[R] =
    def rec(last: Option[R], k: T): Option[R] =
      val sol: Option[R] = search(args1, k)
      sol match {
        case opt: Some[R] => if (cmp(k, end)) rec(opt, succ(k)) else opt
        case _ => last
      }
    rec(None, start)
}

trait BasicMinProblem[A, R] extends BasicOptProblem[A, Int, R]{
  def min(args1: A): Option[R]
  protected def min: (A, Int, Int) =>  Option[R] = opt(_ > _, _ - 1)
}

trait BasicMaxProblem[A, R] extends BasicOptProblem[A, Int, R]{
  def max(args1: A): Option[R]
  protected def max: (A, Int, Int) =>  Option[R] = opt(_ < _, _ + 1)
}

trait BasicMinBiProblem[A, B, R] extends BasicTriProblem[A, B, Int, R] with BasicMinProblem[(A, B), R]{
  def min(args1: A, args2: B): Option[R]
  override def min(args: (A, B)): Option[R] = min(args._1, args._2)
  protected def min(args1: A, args2: B, startingSize: Int, endIdx: Int): Option[R] =
    min((args1, args2), startingSize, endIdx)
}

trait BasicMaxBiProblem[A, B, R] extends BasicTriProblem[A, B, Int, R] with BasicMaxProblem[(A, B), R]{
  def max(args1: A, args2: B): Option[R]
  override def max(args: (A, B)): Option[R] = max(args._1, args._2)
  protected def max(args1: A, args2: B, startingSize: Int, endIdx: Int): Option[R] =
    max((args1, args2), startingSize, endIdx)
}

trait MinProblem[A, R] extends BiProblem[A, Int, R] with BasicMinProblem[A, R]
trait MaxProblem[A, R] extends BiProblem[A, Int, R] with BasicMaxProblem[A, R]
trait MinBiProblem[A, B, R] extends TriProblem[A, B, Int, R] with BasicMinBiProblem[A, B, R]
trait MaxBiProblem[A, B, R] extends TriProblem[A, B, Int, R] with BasicMaxBiProblem[A, B, R]