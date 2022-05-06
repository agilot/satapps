package satapps.problems

import satapps.*
import Z3.{*, given}
import Extensions.*
import z3.scala.*

object Sets {

  /************************Partitioning*****************************/

  private def partitionSetConstraints(s: Seq[Int], k: Int): Z3Type = 
    val str: Seq[String] = for(i <- 0 until s.size; j <- 0 until k) yield s"${i},${j}"
    val vars: Seq[Z3Type] = intConst(str)
    val cst1: Z3Type = vars >= 0
    val cst2: Z3Type = andAll(for(i <- 0 until s.size) yield sum(for(j <- 0 until k) yield intConst(s"${i},${j}")) === 1)
    cst1 && cst2

  private def partitionConstraints(s: Seq[Int], k: Int): Z3Type =
    val tot: Int = s.reduce(_ + _)
    val zs: Seq[(Int, Int)] = s.zipWithIndex
    val cst: Z3Type = andAll(for(j <- 0 until k) yield sum(zs.map((elem, i) => elem * intConst(s"${i},${j}"))) === (tot / k))
    partitionSetConstraints(s, k) && cst
    
  private def knapsackConstraints(items: Seq[(Int, Int)], w: Int, v: Int): Z3Type =
    val zi: Seq[((Int, Int), Int)] = items.zipWithIndex
    val str: Seq[String] = Range(0, items.size).map(_.toString)
    val vars: Seq[Z3Type] = intConst(str)
    val cst1: Z3Type = vars >= 0
    val cst2: Z3Type = sum(zi.map((it, j) => intConst(j.toString) * it._1)) <= w
    val cst3: Z3Type = sum(zi.map((it, j) => intConst(j.toString) * it._2)) >= v
    cst1 && cst2 && cst3


  object Partition extends BasicProblem[MultiSet[Int], (MultiSet[Int], MultiSet[Int])]{
    def search(s: MultiSet[Int]): Option[(MultiSet[Int], MultiSet[Int])] =
      KWayNumberPartitioning.search(s, 2).map(some => (some.head, some.tail.head))
    def decision(s: MultiSet[Int]): Boolean = KWayNumberPartitioning.decision(s, 2)
    def enumeration(s: MultiSet[Int]): Set[(MultiSet[Int], MultiSet[Int])] =
      KWayNumberPartitioning.enumeration(s, 2).map(some => (some.head, some.tail.head))
  }

  object ThreePartition extends BasicProblem[MultiSet[Int], Seq[(Int, Int, Int)]]{
    private def to3Tuple = (m: MultiSet[Int]) =>
        val l: List[Int] = m.toList
        val tl = l.tail
        (l.head, tl.head, tl.tail.head)
    def search(s: MultiSet[Int]): Option[Seq[(Int, Int, Int)]] =
      KPartitioning.search(s, 3).map(_.map(to3Tuple))
    def decision(s: MultiSet[Int]): Boolean = KPartitioning.decision(s, 3)
    def enumeration(s: MultiSet[Int]): Set[Seq[(Int, Int, Int)]] =
      KPartitioning.enumeration(s, 3).map(_.map(to3Tuple))
  }

  object FourPartition extends BasicProblem[MultiSet[Int], Seq[(Int, Int, Int, Int)]]{
    private def to4Tuple = (m: MultiSet[Int]) =>
        val l: List[Int] = m.toList
        val tl = l.tail
        val ttl = tl.tail
        (l.head, tl.head, ttl.head, ttl.tail.head)
    def search(s: MultiSet[Int]): Option[Seq[(Int, Int, Int, Int)]] =
      KPartitioning.search(s, 4).map(_.map(to4Tuple))
    def decision(s: MultiSet[Int]): Boolean = KPartitioning.decision(s, 4)
    def enumeration(s: MultiSet[Int]) = KPartitioning.enumeration(s, 4).map(_.map(to4Tuple))
  }

  object KPartitioning extends BiProblem[MultiSet[Int], Int, Seq[MultiSet[Int]]]{
    override def constraints(s: MultiSet[Int], k: Int) = 
      if (s.size % k == 0)
        val tot: Int = s.reduce(_ + _)
        val n = s.size/k
        if(tot % n == 0)
          val str: Seq[String] = for(i <- 0 until s.size; j <- 0 until n) yield s"${i},${j}"
          val cst: Z3Type = andAll(for(j <- 0 until n) yield sum(for(i <- 0 until s.size) yield intConst(s"${i},${j}")) === k)
          (partitionConstraints(s.toSeq.sorted, n) && cst, str)
        else (false, Nil)
      else (false,  Nil)

    override def convert(s: MultiSet[Int], k: Int, sol: Seq[Z3AST]) =
      val n = s.size/k
      val zsk: Seq[(Int, Int)] = s.toSeq.sorted.flatMap(List.fill(n)(_)).zipWithIndex
      for(j <- 0 until n)
        yield MultiSetFactory.from(toInt(sol).zip(zsk).filter((x, p) => x > 0 && p._2 % n == j).map((x, p) => p._1))
  }

  object KWayNumberPartitioning extends BiProblem[MultiSet[Int], Int, Seq[MultiSet[Int]]]{
    override def constraints(s: MultiSet[Int], k: Int) = 
      require(k >= 1)
      val tot: Int = s.reduce(_ + _)
      if(tot % k == 0)
        val str: Seq[String] = for(i <- 0 until s.size; j <- 0 until k) yield s"${i},${j}"
        (partitionConstraints(s.toSeq.sorted, k), str)
      else (false, Nil)

    override def convert(s: MultiSet[Int], k: Int, sol: Seq[Z3AST]) =
      val zsk: Seq[(Int, Int)] = s.toSeq.sorted.flatMap(List.fill(k)(_)).zipWithIndex
      for(j <- 0 until k) yield MultiSetFactory.from(toInt(sol).zip(zsk).filter((x, p) => x > 0 && p._2 % k == j).map((x, p) => p._1))
    }

  object SubsetSum extends BiProblem[MultiSet[Int], Int, MultiSet[Int]]{
    override def constraints(s: MultiSet[Int], k: Int) = 
      require(k >= 1)
      val tot: Int = s.reduce(_ + _)
      if(tot % k == 0)
        val str: Seq[String] = for(i <- 0 until s.size; j <- 0 until k) yield s"${i},${j}"
        (partitionConstraints(s.toSeq.sorted, k), str)
      else (false, Nil)

    override def convert(s: MultiSet[Int], k: Int, sol: Seq[Z3AST]) = MultiSetFactory.from(filterSol(sol).map(i => s.toSeq.sorted.apply(i)))    
    }

  case class SetPackingGeneric[T]() extends BasicMaxProblem[Seq[Set[T]], Set[Int]]{
    override def search(c: Seq[Set[T]], k: Int): Option[Set[Int]] =
      val z = c.zipWithIndex
      val g = Graph(Range(0, c.size).toSet, (for(p1 <- z; p2 <- z; if (p1._2 != p2._2) && ((p1._1 & p2._1) != Set()))
        yield (p1._2, p2._2)).toSet)
      satapps.problems.Graphs.Indset.search(g,k)
    override def decision(c: Seq[Set[T]], k: Int): Boolean = search(c, k).isDefined
    override def enumeration(c: Seq[Set[T]], k: Int): Set[Set[Int]] =
      val z = c.zipWithIndex
      val g = Graph(Range(0, c.size).toSet, (for(p1 <- z; p2 <- z; if (p1._2 != p2._2) && ((p1._1 & p2._1) != Set()))
        yield (p1._2, p2._2)).toSet)
      satapps.problems.Graphs.Indset.enumeration(g,k)

    override def max(c: Seq[Set[T]]) = max(c, 1, c.size)
  }
  
  def SetPacking[T]: SetPackingGeneric[T] = SetPackingGeneric[T]()

  case class SetCoverGeneric[T]() extends MinBiProblem[Set[T], Seq[Set[T]], Set[Int]]{
    override def constraints(u: Set[T], c: Seq[Set[T]], k: Int) =
      if (c.foldLeft(u)(_ -- _) == Set())
        val zc: Seq[(Set[T], Int)] = c.zipWithIndex
        val str: Seq[String] = Range(0, c.size).map(_.toString)
        val vars: Seq[Z3Type] = intConst(str)
        val cst1: Z3Type = vars >= 0
        val cst2: Z3Type = andAll((for elem <- u yield sum(zc.filter((s, j) => s.contains(elem)).map(e => intConst(e._2.toString))) >= 1).toList)
        val cst3: Z3Type = sum(vars) <= k
        (cst1 && cst2 && cst3, str)
      else (false, Nil)
    
    override def convert(u: Set[T], c: Seq[Set[T]], k: Int, sol: Seq[Z3AST]) = filterSol(sol).toSet

    override def min(u: Set[T], c: Seq[Set[T]]) = min(u, c, c.size, 1)
  }

  def SetCover[T]: SetCoverGeneric[T] = SetCoverGeneric[T]()

  case class ExactCoverGeneric[T]() extends BiProblem[Set[T], Seq[Set[T]], Set[Int]]{
    override def constraints(u: Set[T], c: Seq[Set[T]]) =
      if (c.foldLeft(u)(_ -- _) == Set())
        val zc: Seq[(Set[T], Int)] = c.zipWithIndex
        val str: Seq[String] = Range(0, c.size).map(_.toString)
        val vars: Seq[Z3Type] = intConst(str)
        val cst1: Z3Type = vars >= 0
        val cst2: Z3Type = andAll((for elem <- u yield sum(zc.filter((s, j) => s.contains(elem)).map(e => intConst(e._2.toString))) === 1).toList)
        (cst1 && cst2, str)
      else (false, Nil)
    
    override def convert(u: Set[T], c: Seq[Set[T]], sol: Seq[Z3AST]) = filterSol(sol).toSet
  }

  def ExactCover[T]: ExactCoverGeneric[T] = ExactCoverGeneric[T]()

  case class SetSplitting[T]() extends BiProblem[Set[T], Seq[Set[T]], (Set[T], Set[T])]{
    override def constraints(u: Set[T], c: Seq[Set[T]]) =
      if (c.foldLeft(u)(_ -- _) == Set())
        val lu: Seq[T] = u.toSeq
        val mu: Map[T, Int] = u.zipWithIndex.toMap
        val str: Seq[String] = Range(0, u.size).map(_.toString)
        val vars: Seq[Z3Type] = intConst(str)
        val cst1: Z3Type = vars >= 0 && vars <= 1
        val cst2: Z3Type = andAll(for(s <- c) yield 
          val summ = sum((for(e <- s) yield intConst(mu(e).toString)).toSeq)
          summ > 0 && summ < s.size)
        (cst1 && cst2, str)
      else (false, Nil)
    
    override def convert(u: Set[T], c: Seq[Set[T]], sol: Seq[Z3AST]): (Set[T], Set[T]) = 
      val res: Set[T] = filterSol(sol).map(u.toSeq(_)).toSet;
      (res, u -- res)
  }

  object BinPacking extends MinBiProblem[MultiSet[Int], Int, Seq[MultiSet[Int]]]{
    override def constraints(s: MultiSet[Int], b: Int, k: Int) =
      val sl: Seq[Int] = s.toSeq.sorted
      val str: Seq[String] = for(i <- 0 until s.size; j <- 0 until k) yield s"${i},${j}"
      val zs: Seq[(Int, Int)] = sl.zipWithIndex
      val cst: Z3Type = andAll(for(j <- 0 until k) yield sum(zs.map((elem, i) => elem * intConst(s"${i},${j}"))) <= b)
      (partitionSetConstraints(sl, k) && cst, str)

    override def convert(s: MultiSet[Int], b: Int, k: Int, sol: Seq[Z3AST]): Seq[MultiSet[Int]] =
      val zsk: Seq[(Int, Int)] = s.toSeq.sorted.flatMap(List.fill(k)(_)).zipWithIndex
      for(j <- 0 until k)
        yield MultiSetFactory.from(toInt(sol).zip(zsk).filter((x, p) => x > 0 && p._2 % k == j).map((x, p) => p._1))
    
    override def min(s: MultiSet[Int], b: Int): Option[Seq[MultiSet[Int]]] = min(s, b, s.size, 0)
  }

  object BoundedKnapsack extends QuadriProblem[Seq[(Int, Int)], Int, Int, Int, Seq[Int]]{
    override def constraints(items: Seq[(Int, Int)], w: Int, c: Int, v: Int) =
      val str: Seq[String] = Range(0, items.size).map(_.toString)
      (knapsackConstraints(items, w, v) && (intConst(str) <= c), str)
    
    override def convert(items: Seq[(Int, Int)], w: Int, c: Int, v: Int, sol: Seq[Z3AST]) = toInt(sol)
  }

  object Knapsack extends BasicTriProblem[Seq[(Int, Int)], Int, Int, Seq[Int]]{
    override def search(items: Seq[(Int, Int)], w: Int, v: Int) = BoundedKnapsack.search(items, w, 1, v)
    override def decision(items: Seq[(Int, Int)], w: Int, v: Int) = BoundedKnapsack.decision(items, w, 1, v)
    override def enumeration(items: Seq[(Int, Int)], w: Int, v: Int) = BoundedKnapsack.enumeration(items, w, 1, v)
  }

  object UnboundedKnapsack extends TriProblem[Seq[(Int, Int)], Int, Int, Seq[Int]]{
    override def constraints(items: Seq[(Int, Int)], w: Int, v: Int) = 
      val str: Seq[String] = Range(0, items.size).map(_.toString)
      (knapsackConstraints(items, w, v), str)
    override def convert(items: Seq[(Int, Int)], w: Int, v: Int, sol: Seq[Z3AST]) = toInt(sol)
  }


}