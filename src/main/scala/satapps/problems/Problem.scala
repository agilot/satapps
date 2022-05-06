package satapps.problems

import satapps.*
import Z3.{*, given}
import BooleanMatricesOps.{*, given}
import scala.collection.immutable.ArraySeq
import Extensions.*
import z3.scala.*

trait BasicProblem[A, R]{
  def search(args: A): Option[R]
  def decision(args: A): Boolean
  def enumeration(args: A): Set[R]
}

trait BasicBiProblem[A, B, R] extends BasicProblem[(A, B), R]{
  override def search(args: (A, B)): Option[R] = search(args._1, args._2)
  override def decision(args: (A, B)): Boolean = decision(args._1, args._2)
  override def enumeration(args: (A, B)): Set[R] = enumeration(args._1, args._2)
  def search(args1: A, args2: B): Option[R]
  def decision(args1: A, args2: B): Boolean
  def enumeration(args1: A, args2: B): Set[R]
}

trait BasicTriProblem[A, B, C, R] extends BasicBiProblem[(A, B), C, R]{
  override def search(args1: (A, B), args2: C): Option[R] = search(args1._1, args1._2, args2)
  override def decision(args1: (A, B), args2: C): Boolean = decision(args1._1, args1._2, args2)
  override def enumeration(args1: (A, B), args2: C): Set[R] = enumeration(args1._1, args1._2, args2)
  def search(args1: A, args2: B, args3: C): Option[R]
  def decision(args1: A, args2: B, args3: C): Boolean
  def enumeration(args1: A, args2: B, args3: C): Set[R]
}

trait BasicQuadriProblem[A, B, C, D, R] extends BasicTriProblem[(A, B), C, D, R]{
  override def search(args1: (A, B), args2: C, args3: D): Option[R] = search(args1._1, args1._2, args2, args3)
  override def decision(args1: (A, B), args2: C, args3: D): Boolean = decision(args1._1, args1._2, args2, args3)
  override def enumeration(args1: (A, B), args2: C, args3: D): Set[R] = enumeration(args1._1, args1._2, args2, args3)
  def search(args1: A, args2: B, args3: C, args4: D): Option[R]
  def decision(args1: A, args2: B, args3: C, args4: D): Boolean
  def enumeration(args1: A, args2: B, args3: C, args4: D): Set[R]
}

trait Problem[A, R] extends BasicProblem[A, R]{
  protected def constraints(args: A): (Z3Type, Seq[String])
  protected def solution(args: A): (Option[Seq[Z3AST]], Z3Context) = 
    val (cst, str) = constraints(args)
    solve(cst, str)

  protected def convert(args: A, sol: Seq[Z3AST]): R

  def search(args: A): Option[R] =
    val (sol, z) = solution(args)
    val res = sol.map(convert(args, _))
    z.delete()
    res
  def decision(args: A): Boolean = 
    val (sol, z) = solution(args)
    val res = sol.isDefined
    z.delete()
    res
  def enumeration(args: A): Set[R] =
    val (firstCst, str) = constraints(args)

    def newCst(sol: Seq[Z3AST]): Z3Type =
      orAll(intConst(str).zip(toInt(sol)).map(_ !== _))

    def rec(cst: Z3Type): Set[R] =
      solve(cst, str) match{
        case(None, z) => 
          z.delete()
          Set()
        case(Some(s), z) =>
          val res = convert(args, s)
          z.delete()
          rec(cst && newCst(s)) + res
      }
    rec(firstCst)
}

trait BiProblem[A, B, R] extends Problem[(A, B), R] with BasicBiProblem[A, B, R]{

  protected def constraints(args1: A, args2: B): (Z3Type, Seq[String])
  protected def convert(args1: A, args2: B, sol: Seq[Z3AST]): R
  override protected def constraints(args: (A, B)): (Z3Type, Seq[String]) = constraints(args._1, args._2)
  override protected def convert(args: (A, B), sol: Seq[Z3AST]): R = convert(args._1, args._2, sol)

  override def search(args1: A, args2: B): Option[R] = super[Problem].search((args1, args2))
  override def decision(args1: A, args2: B): Boolean = super[Problem].decision((args1, args2))
  override def enumeration(args1: A, args2: B): Set[R] = super[Problem].enumeration((args1, args2))
}

trait TriProblem[A, B, C, R] extends BiProblem[(A, B), C, R] with BasicTriProblem[A, B, C, R]{

  protected def constraints(args1: A, args2: B, args3: C): (Z3Type, Seq[String])
  protected def convert(args1: A, args2: B, args3: C, sol: Seq[Z3AST]): R
  override protected def constraints(args1: (A, B), args2: C): (Z3Type, Seq[String]) = constraints(args1._1, args1._2, args2)
  override protected def convert(args1: (A, B), args2: C, sol: Seq[Z3AST]): R = convert(args1._1, args1._2, args2, sol)

  override def search(args1: A, args2: B, args3: C): Option[R] = super[BiProblem].search((args1, args2), args3)
  override def decision(args1: A, args2: B, args3: C): Boolean = super[BiProblem].decision((args1, args2), args3)
  override def enumeration(args1: A, args2: B, args3: C): Set[R] = super[BiProblem].enumeration((args1, args2), args3)
}

trait QuadriProblem[A, B, C, D, R] extends TriProblem[(A, B), C, D, R] with BasicQuadriProblem[A, B, C, D, R]{

  protected def constraints(args1: A, args2: B, args3: C, args4: D): (Z3Type, Seq[String])
  protected def convert(args1: A, args2: B, args3: C, args4: D, sol: Seq[Z3AST]): R
  override protected def constraints(args1: (A, B), args2: C, args3: D): (Z3Type, Seq[String]) = constraints(args1._1, args1._2, args2, args3)
  override protected def convert(args1: (A, B), args2: C, args3: D, sol: Seq[Z3AST]): R = convert(args1._1, args1._2, args2, args3, sol)

  override def search(args1: A, args2: B, args3: C, args4: D): Option[R] = super[TriProblem].search((args1, args2), args3, args4)
  override def decision(args1: A, args2: B, args3: C, args4: D): Boolean = super[TriProblem].decision((args1, args2), args3, args4)
  override def enumeration(args1: A, args2: B, args3: C, args4: D): Set[R] = super[TriProblem].enumeration((args1, args2), args3, args4)
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