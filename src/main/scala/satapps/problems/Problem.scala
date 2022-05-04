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
}

trait BasicBiProblem[A, B, R] extends BasicProblem[(A, B), R]{
  override def search(args: (A, B)): Option[R] = search(args._1, args._2)
  override def decision(args: (A, B)): Boolean = decision(args._1, args._2)
  def search(args1: A, args2: B): Option[R]
  def decision(args1: A, args2: B): Boolean
}

trait BasicTriProblem[A, B, C, R] extends BasicBiProblem[(A, B), C, R]{
  override def search(args1: (A, B), args2: C): Option[R] = search(args1._1, args1._2, args2)
  override def decision(args1: (A, B), args2: C): Boolean = decision(args1._1, args1._2, args2)
  def search(args1: A, args2: B, args3: C): Option[R]
  def decision(args1: A, args2: B, args3: C): Boolean
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
}

trait BiProblem[U, V, W] extends Problem[(U, V), W] with BasicBiProblem[U, V, W]{

  protected def constraints(args1: U, args2: V): (Z3Type, Seq[String])
  protected def convert(args1: U, args2: V, sol: Seq[Z3AST]): W
  override protected def constraints(args: (U, V)): (Z3Type, Seq[String]) = constraints(args._1, args._2)
  override protected def convert(args: (U, V), sol: Seq[Z3AST]): W = convert(args._1, args._2, sol)

  override def search(args1: U, args2: V): Option[W] = super[Problem].search((args1, args2))
  override def decision(args1: U, args2: V): Boolean = super[Problem].decision((args1, args2))
}

trait TriProblem[A, B, C, R] extends BiProblem[(A, B), C, R] with BasicTriProblem[A, B, C, R]{

  protected def constraints(args1: A, args2: B, args3: C): (Z3Type, Seq[String])
  protected def convert(args1: A, args2: B, args3: C, sol: Seq[Z3AST]): R
  override protected def constraints(args1: (A, B), args2: C): (Z3Type, Seq[String]) = constraints(args1._1, args1._2, args2)
  override protected def convert(args1: (A, B), args2: C, sol: Seq[Z3AST]): R = convert(args1._1, args1._2, args2, sol)

  override def search(args1: A, args2: B, args3: C): Option[R] = super[BiProblem].search((args1, args2), args3)
  override def decision(args1: A, args2: B, args3: C): Boolean = super[BiProblem].decision((args1, args2), args3)
}

trait BasicMinProblem[A, R] extends BasicBiProblem[A, Int, R]{
  def min(args1: A): R
  protected def min(args1: A, start: R, startingSize: Int, endIdx: Int): R =
    def rec(last: R, k: Int): R =
      val sol: Option[R] = search(args1, k)
      sol match {
        case Some(s) if k > endIdx => rec(s, k - 1)
        case _ => last
      }
    rec(start, startingSize - 1)
}

trait BasicMaxProblem[A, R] extends BasicBiProblem[A, Int, R]{
  def max(args1: A): R
  protected def max(args1: A, start: R, startingSize: Int, endIdx: Int): R =
    def rec(last: R, k: Int): R =
      val sol: Option[R] = search(args1, k)
      sol match {
        case Some(s) if k < endIdx => rec(s, k + 1)
        case _ => last
      }
    rec(start, startingSize + 1)
}

trait MinProblem[A, R] extends BiProblem[A, Int, R] with BasicMinProblem[A, R]
trait MaxProblem[A, R] extends BiProblem[A, Int, R] with BasicMaxProblem[A, R]