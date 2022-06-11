package satapps.problems

import satapps.*
import ConstrProg.{*, given}
import Extensions.*
import Iter.*
import scala.collection.immutable.ArraySeq

object Sets {

  private def filterIdx(q: NumQuery): Set[Vertex] = q.toInt.filterPositive.varSet.map(_.toInt)


  /************************Partitioning*****************************/

  private def partitionSetConstraints(s: Seq[Int], k: Int): BoolConstr = 
    val vars: Seq[IntConstr] = IntVar(cartesian(Range(0, s.size), Range(0, k)).toSeq)
    val cst1: BoolConstr = vars >= 0
    val cst2: BoolConstr = And(for(i <- 0 until s.size) yield Add(for(j <- 0 until k) yield IntVar((i, j))) === 1)
    cst1 && cst2

  private def partitionConstraints(s: Seq[Int], k: Int): BoolConstr =
    val tot: Int = s.reduce(_ + _)
    val zs: Seq[(Int, Int)] = s.zipWithIndex
    val cst: BoolConstr = And(for(j <- 0 until k) yield Add(zs.map((elem, i) => elem * IntVar((i, j)))) === (tot / k))
    partitionSetConstraints(s, k) && cst
    
  private def knapsackConstraints(items: Seq[(Int, Int)], w: Int, v: Int): BoolConstr =
    val zi: Seq[((Int, Int), Int)] = items.zipWithIndex
    val vars: Seq[IntConstr] = IntVar(Range(0, items.size))
    val cst1: BoolConstr = vars >= 0
    val cst2: BoolConstr = Add(zi.map((it, j) => IntVar(j) * it._1)) <= w
    val cst3: BoolConstr = Add(zi.map((it, j) => IntVar(j) * it._2)) >= v
    cst1 && cst2 && cst3


  object Partition extends BasicProblem[MultiSet[Int], (MultiSet[Int], MultiSet[Int])]{
    def search(s: MultiSet[Int]): Option[(MultiSet[Int], MultiSet[Int])] =
      KWayNumberPartitioning.search(s, 2).map(some => (some.head, some.tail.head))
    def decide(s: MultiSet[Int]): Boolean = KWayNumberPartitioning.decide(s, 2)
    def enumerate(s: MultiSet[Int]): Set[(MultiSet[Int], MultiSet[Int])] =
      KWayNumberPartitioning.enumerate(s, 2).map(some => (some.head, some.tail.head))
    override def verify(s: MultiSet[Int], sol: (MultiSet[Int], MultiSet[Int])) = ??? 
  }

  object ThreePartition extends BasicProblem[MultiSet[Int], Seq[(Int, Int, Int)]]{
    private def to3Tuple = (m: MultiSet[Int]) =>
        val l: List[Int] = m.toList
        val tl = l.tail
        (l.head, tl.head, tl.tail.head)
    def search(s: MultiSet[Int]): Option[Seq[(Int, Int, Int)]] =
      KPartitioning.search(s, 3).map(_.map(to3Tuple))
    def decide(s: MultiSet[Int]): Boolean = KPartitioning.decide(s, 3)
    def enumerate(s: MultiSet[Int]): Set[Seq[(Int, Int, Int)]] =
      KPartitioning.enumerate(s, 3).map(_.map(to3Tuple))
    override def verify(s: MultiSet[Int], sol: Seq[(Int, Int, Int)]) = ??? 
  }

  object FourPartition extends BasicProblem[MultiSet[Int], Seq[(Int, Int, Int, Int)]]{
    private def to4Tuple = (m: MultiSet[Int]) =>
        val l: List[Int] = m.toList
        val tl = l.tail
        val ttl = tl.tail
        (l.head, tl.head, ttl.head, ttl.tail.head)
    def search(s: MultiSet[Int]): Option[Seq[(Int, Int, Int, Int)]] =
      KPartitioning.search(s, 4).map(_.map(to4Tuple))
    def decide(s: MultiSet[Int]): Boolean = KPartitioning.decide(s, 4)
    def enumerate(s: MultiSet[Int]) = KPartitioning.enumerate(s, 4).map(_.map(to4Tuple))
    override def verify(s: MultiSet[Int], sol: Seq[(Int, Int, Int, Int)]) = ??? 
  }

  object KPartitioning extends BiProblem[MultiSet[Int], Int, Seq[MultiSet[Int]]]{
    override def constraints(s: MultiSet[Int], k: Int) = 
      if (s.size % k == 0)
        val tot: Int = s.reduce(_ + _)
        val n = s.size/k
        if(tot % n == 0)
          val cst: BoolConstr = And(for(j <- 0 until n) yield Add(for(i <- 0 until s.size) yield IntVar((i, j))) === k)
          partitionConstraints(s.toSeq.sorted, n) && cst
        else false
      else false

    override def convert(s: MultiSet[Int], k: Int, sol: NumQuery) =
      val seq = s.toIndexedSeq.sorted
      sol.toInt.filterPairIdx.foldLeft(ArraySeq.fill(s.size/k)(MultiSet(): MultiSet[Int]))((acc, p) => acc.updated(p._2, acc(p._2) + seq(p._1)))
    override def verify(s: MultiSet[Int], k: Int, sol: Seq[MultiSet[Int]]) = ??? 
  }

  object KWayNumberPartitioning extends BiProblem[MultiSet[Int], Int, Seq[MultiSet[Int]]]{
    override def constraints(s: MultiSet[Int], k: Int) = 
      require(k >= 1)
      val tot: Int = s.reduce(_ + _)
      if(tot % k == 0)
        partitionConstraints(s.toSeq.sorted, k)
      else false

    override def convert(s: MultiSet[Int], k: Int, sol: NumQuery) =
      val seq = s.toIndexedSeq.sorted
      sol.toInt.filterPairIdx.foldLeft(ArraySeq.fill(k)(MultiSet(): MultiSet[Int]))((acc, p) => acc.updated(p._2, acc(p._2) + seq(p._1)))
    override def verify(s: MultiSet[Int], k: Int, sol: Seq[MultiSet[Int]]) = ??? 
    }

  object SubsetSum extends BiProblem[MultiSet[Int], Int, MultiSet[Int]]{
    override def constraints(s: MultiSet[Int], k: Int) = 
      require(k >= 1)
      val tot: Int = s.reduce(_ + _)
      if(tot % k == 0)
        partitionConstraints(s.toSeq.sorted, k)
      else false

    override def convert(s: MultiSet[Int], k: Int, sol: NumQuery) = 
      val seq = s.toIndexedSeq.sorted
      MultiSetFactory.from(sol.toInt.filterIdx).map(seq(_))

    override def verify(s: MultiSet[Int], k: Int, sol: MultiSet[Int]) = ???    
    }

  case class SetPackingGeneric[T]() extends BasicMaxProblem[Seq[Set[T]], Set[Int]]{
    override def search(c: Seq[Set[T]], k: Int): Option[Set[Int]] =
      val z = c.zipWithIndex
      val g = Graph(Range(0, c.size).toSet, (for(p1 <- z; p2 <- z; if (p1._2 != p2._2) && ((p1._1 & p2._1) != Set()))
        yield (p1._2, p2._2)).toSet)
      satapps.problems.Graphs.Indset.search(g,k)
    override def decide(c: Seq[Set[T]], k: Int): Boolean = search(c, k).isDefined
    override def enumerate(c: Seq[Set[T]], k: Int): Set[Set[Int]] =
      val z = c.zipWithIndex
      val g = Graph(Range(0, c.size).toSet, (for(p1 <- z; p2 <- z; if (p1._2 != p2._2) && ((p1._1 & p2._1) != Set()))
        yield (p1._2, p2._2)).toSet)
      satapps.problems.Graphs.Indset.enumerate(g,k)
    override def verify(c: Seq[Set[T]], k: Int, sol: Set[Int]) = ???
    override def max(c: Seq[Set[T]]) = max(c, 1, c.size)
  }
  
  def SetPacking[T]: SetPackingGeneric[T] = SetPackingGeneric[T]()

  case class SetCoverGeneric[T]() extends MinBiProblem[Set[T], Seq[Set[T]], Set[Int]]{
    override def constraints(u: Set[T], c: Seq[Set[T]], k: Int) =
      if (c.foldLeft(u)(_ -- _) == Set())
        val zc: Seq[(Set[T], Int)] = c.zipWithIndex
        val vars: Seq[IntConstr] = IntVar(Range(0, c.size))
        val cst1: BoolConstr = vars >= 0
        val cst2: BoolConstr = And((for elem <- u yield Add(zc.filter((s, j) => s.contains(elem)).map(e => IntVar(e._2))) >= 1).toList)
        val cst3: BoolConstr = Add(vars) <= k
        cst1 && cst2 && cst3
      else false
    
    override def convert(u: Set[T], c: Seq[Set[T]], k: Int, sol: NumQuery) = filterIdx(sol)
    override def verify(u: Set[T], c: Seq[Set[T]], k: Int, sol: Set[Int]) = ???
    override def min(u: Set[T], c: Seq[Set[T]]) = min(u, c, c.size, 1)
  }

  def SetCover[T]: SetCoverGeneric[T] = SetCoverGeneric[T]()

  case class ExactCoverGeneric[T]() extends BiProblem[Set[T], Seq[Set[T]], Set[Int]]{
    override def constraints(u: Set[T], c: Seq[Set[T]]) =
      if (c.foldLeft(u)(_ -- _) == Set())
        val zc: Seq[(Set[T], Int)] = c.zipWithIndex
        val vars: Seq[IntConstr] = IntVar(Range(0, c.size))
        val cst1: BoolConstr = vars >= 0
        val cst2: BoolConstr = And((for elem <- u yield Add(zc.filter((s, j) => s.contains(elem)).map(e => IntVar(e._2))) === 1).toList)
        cst1 && cst2
      else false
    
    override def convert(u: Set[T], c: Seq[Set[T]], sol: NumQuery) = filterIdx(sol)
    override def verify(u: Set[T], c: Seq[Set[T]], sol: Set[Int]) = 
      val ca = c.toIndexedSeq
      c.foldLeft(u)(_ -- _).isEmpty
  }

  def ExactCover[T]: ExactCoverGeneric[T] = ExactCoverGeneric[T]()

  case class SetSplitting[T]() extends BiProblem[Set[T], Seq[Set[T]], (Set[T], Set[T])]{
    override def constraints(u: Set[T], c: Seq[Set[T]]) =
      if (c.foldLeft(u)(_ -- _) == Set())
        val lu: Seq[T] = u.toSeq
        val mu: Map[T, Int] = u.zipWithIndex.toMap
        val vars: Seq[IntConstr] = IntVar(Range(0, u.size))
        val cst1: BoolConstr = vars >= 0 && vars <= 1
        val cst2: BoolConstr = And(for(s <- c) yield 
          val summ = Add((for(e <- s) yield IntVar(mu(e))).toSeq)
          summ > 0 && summ < s.size)
        cst1 && cst2
      else false
    
    override def convert(u: Set[T], c: Seq[Set[T]], sol: NumQuery): (Set[T], Set[T]) = 
      val res: Set[T] = filterIdx(sol).map(u.toSeq(_));
      (res, u -- res)
    override def verify(u: Set[T], c: Seq[Set[T]], sol: (Set[T], Set[T])) = ???
  }

  object BinPacking extends MinBiProblem[MultiSet[Int], Int, Seq[MultiSet[Int]]]{
    override def constraints(s: MultiSet[Int], b: Int, k: Int) =
      val sl: Seq[Int] = s.toSeq.sorted
      val str: Seq[String] = for(i <- 0 until s.size; j <- 0 until k) yield s"${i},${j}"
      val zs: Seq[(Int, Int)] = sl.zipWithIndex
      val cst: BoolConstr = And(for(j <- 0 until k) yield Add(zs.map((elem, i) => elem * IntVar((i, j)))) <= b)
      partitionSetConstraints(sl, k) && cst

    override def convert(s: MultiSet[Int], b: Int, k: Int, sol: NumQuery): Seq[MultiSet[Int]] =
      val seq = s.toIndexedSeq.sorted
      sol.toInt.filterPairIdx.foldLeft(ArraySeq.fill(k)(MultiSet(): MultiSet[Int]))((acc, p) => acc.updated(p._2, acc(p._2) + seq(p._1)))
    override def verify(s: MultiSet[Int], b: Int, k: Int, sol: Seq[MultiSet[Int]]) = ???
    override def min(s: MultiSet[Int], b: Int): Option[Seq[MultiSet[Int]]] = min(s, b, s.size, 0)
  }

  object BoundedKnapsack extends QuadriProblem[Seq[(Int, Int)], Int, Int, Int, Set[Int]]{
    override def constraints(items: Seq[(Int, Int)], w: Int, c: Int, v: Int) = knapsackConstraints(items, w, v) && (IntVar(Range(0, items.size)) <= c)
    override def convert(items: Seq[(Int, Int)], w: Int, c: Int, v: Int, sol: NumQuery) = filterIdx(sol)
    override def verify(items: Seq[(Int, Int)], w: Int, c: Int, v: Int, sol: Set[Int]) = ???
  }

  object Knapsack extends BasicTriProblem[Seq[(Int, Int)], Int, Int, Set[Int]]{
    override def search(items: Seq[(Int, Int)], w: Int, v: Int) = BoundedKnapsack.search(items, w, 1, v)
    override def decide(items: Seq[(Int, Int)], w: Int, v: Int) = BoundedKnapsack.decide(items, w, 1, v)
    override def enumerate(items: Seq[(Int, Int)], w: Int, v: Int) = BoundedKnapsack.enumerate(items, w, 1, v)
    override def verify(items: Seq[(Int, Int)], w: Int, v: Int, sol: Set[Int]) = ???
  }

  object UnboundedKnapsack extends TriProblem[Seq[(Int, Int)], Int, Int, Set[Int]]{
    override def constraints(items: Seq[(Int, Int)], w: Int, v: Int) = knapsackConstraints(items, w, v)
    override def convert(items: Seq[(Int, Int)], w: Int, v: Int, sol: NumQuery) = filterIdx(sol)
    override def verify(items: Seq[(Int, Int)], w: Int, v: Int, sol: Set[Int]) = ???
  }


}