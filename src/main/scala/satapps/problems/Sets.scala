package satapps.problems

import satapps.*
import Z3.{*, given}
import Extensions.*

object Sets {

  /************************Partitioning*****************************/
  def partition(s: MultiSet[Int]): Option[(MultiSet[Int], MultiSet[Int])] =
    kWayNumberPartitioning(s, 2).map(some => (some.head, some.tail.head))

  def partitionDecision(s: MultiSet[Int]): Boolean = partition(s).isDefined

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

  def threePartition(s: MultiSet[Int]): Option[Seq[(Int, Int, Int)]] =
    kPartitioning(s, 3).map(_.map( m =>
      val l: List[Int] = m.toList
      val tl = l.tail
      (l.head, tl.head, tl.tail.head)
    ))

  def fourPartition(s: MultiSet[Int]): Option[Seq[(Int, Int, Int, Int)]] =
    kPartitioning(s, 4).map(_.map( m =>
      val l: List[Int] = m.toList
      val tl = l.tail
      val ttl = tl.tail
      (l.head, tl.head, ttl.head, ttl.tail.head)
    ))

  def kPartitioning(s: MultiSet[Int], k: Int): Option[Seq[MultiSet[Int]]] =
    if (s.size % k == 0)
      val tot: Int = s.reduce(_ + _)
      val n = s.size/k
      if(tot % n == 0)
        val sl: Seq[Int] = s.toSeq
        val str: Seq[String] = for(i <- 0 until s.size; j <- 0 until n) yield s"${i},${j}"
        val cst: Z3Type = andAll(for(j <- 0 until n) yield sum(for(i <- 0 until s.size) yield intConst(s"${i},${j}")) === k)
        val (sol, z) = solve(partitionConstraints(sl, n) && cst, str)

        val zsk: Seq[(Int, Int)] = sl.flatMap(List.fill(n)(_)).zipWithIndex
        val res: Option[Seq[MultiSet[Int]]] = 
          toInt(sol).map( some => 
            for(j <- 0 until n)
              yield MultiSetFactory.from(some.zip(zsk).filter((x, p) => x > 0 && p._2 % n == j).map((x, p) => p._1))
          )
        z.delete()
        res
      else None
    else None

  def kPartitioningDecision(s: MultiSet[Int], k: Int): Boolean = kPartitioning(s, k).isDefined

  def subsetSum(s: MultiSet[Int], b: Int): Option[(MultiSet[Int], MultiSet[Int])] =
    val sl: Seq[Int] = s.toIndexedSeq
    val tot: Int = sl.reduce(_ + _)
    val zs: Seq[(Int, Int)] = sl.zipWithIndex
    val str: Seq[String] = for(i <- 0 until s.size) yield i.toString
    val cst: Z3Type = sum(zs.map((elem, i) => elem * intConst(s"${i}"))) === b
    val (sol, z) = solve(cst, str)
    val s1: Option[MultiSet[Int]] = filterSol(sol).map(opt => MultiSetFactory.from(opt.map(i => sl(i))))
    s1.map(set1 => (set1, s -- set1))

  def subsetSumDecision(s: MultiSet[Int], b: Int): Boolean = subsetSum(s, b).isDefined

  def kWayNumberPartitioning(s: MultiSet[Int], k: Int): Option[Seq[MultiSet[Int]]] =
    require(k >= 1)
    if (k == 1)
      Some(List(s))
    else
      val tot: Int = s.reduce(_ + _)
      if(tot % k == 0)
        val sl: Seq[Int] = s.toSeq
        val str: Seq[String] = for(i <- 0 until s.size; j <- 0 until k) yield s"${i},${j}"
        val (sol, z) = solve(partitionConstraints(sl, k), str)

        val zsk: Seq[(Int, Int)] = sl.flatMap(List.fill(k)(_)).zipWithIndex
        val res: Option[Seq[MultiSet[Int]]] = 
          toInt(sol).map( some => 
            for(j <- 0 until k)
              yield MultiSetFactory.from(some.zip(zsk).filter((x, p) => x > 0 && p._2 % k == j).map((x, p) => p._1))
          )
        z.delete()
        res
      else None
  
  def kWayNumberPartitioningDecision(s: MultiSet[Int], k: Int): Boolean = kWayNumberPartitioning(s, k).isDefined

  /**/
  def setPacking[T](k: Int, c: Seq[Set[T]]): Option[Set[Int]] =
    val z = c.zipWithIndex
    val g = Graph(Range(0, c.size).toSet, (for(p1 <- z; p2 <- z; if (p1._2 != p2._2) && ((p1._1 & p2._1) != Set()))
      yield (p1._2, p2._2)).toSet)
    satapps.problems.Graphs.Indset.search(g,k)

  def setCover[T](u: Set[T], c: Seq[Set[T]])(k: Int): Option[Set[Int]] =
    require(k > 0)
    if (c.foldLeft(u)(_ -- _) == Set())
      val zc: Seq[(Set[T], Int)] = c.zipWithIndex
      val str: Seq[String] = Range(0, c.size).map(_.toString)
      val vars: Seq[Z3Type] = intConst(str)
      val cst1: Z3Type = vars >= 0
      val cst2: Z3Type = andAll((for elem <- u yield sum(zc.filter((s, j) => s.contains(elem)).map(e => intConst(e._2.toString))) >= 1).toList)
      val cst3: Z3Type = sum(vars) <= k
      val (sol, z) = solve(cst1 && cst2 && cst3, str)
      val res = filterSol(sol).map(_.toSet)
      z.delete()
      res
    else None

  def exactCover[T](u: Set[T], c: Seq[Set[T]]): Option[Set[Int]] =
    if (c.foldLeft(u)(_ -- _) == Set())
      val zc: Seq[(Set[T], Int)] = c.zipWithIndex
      val str: Seq[String] = Range(0, c.size).map(_.toString)
      val vars: Seq[Z3Type] = intConst(str)
      val cst1: Z3Type = vars >= 0
      val cst2: Z3Type = andAll((for elem <- u yield sum(zc.filter((s, j) => s.contains(elem)).map(e => intConst(e._2.toString))) === 1).toList)
      val (sol, z) = solve(cst1 && cst2, str)
      val res = filterSol(sol).map(_.toSet)
      z.delete()
      res
    else None

  // def minSetCover[T](u: Set[T], c: Seq[Set[T]]): Set[Int] =
  //   min(Range(0, c.size).toSet, c.size - 1, setCover(u, c), 1)

  def setSplitting[T](u: Set[T], c: Seq[Set[T]]): Option[(Set[T], Set[T])] = 
    if (c.foldLeft(u)(_ -- _) == Set())
      val lu: Seq[T] = u.toSeq
      val mu: Map[T, Int] = u.zipWithIndex.toMap
      val str: Seq[String] = Range(0, u.size).map(_.toString)
      val vars: Seq[Z3Type] = intConst(str)
      val cst1: Z3Type = vars >= 0 && vars <= 1
      val cst2: Z3Type = andAll(for(s <- c) yield 
        val summ = sum((for(e <- s) yield intConst(mu(e).toString)).toSeq)
        summ > 0 && summ < s.size)
      val (sol, z) = solve(cst1 && cst2, str)
      val res = filterSol(sol).map(_.toSet)
      z.delete()
      res.map((some: Set[Int]) => 
        val someT: Set[T] = some.map(lu(_)) 
        (someT, u -- someT))
    else None

  def setSplittingDecision[T](u: Set[T], c: Seq[Set[T]]): Boolean = setSplitting(u, c).isDefined




  def binPacking(s: MultiSet[Int], k: Int, b: Int): Option[Seq[MultiSet[Int]]] = 
    require(k >= 1)
    if (k == 1)
      if (s.reduce(_ + _) <= b) Some(List(s)) else None
    else
      val sl: Seq[Int] = s.toSeq
      val str: Seq[String] = for(i <- 0 until s.size; j <- 0 until k) yield s"${i},${j}"
      val zs: Seq[(Int, Int)] = sl.zipWithIndex
      val cst: Z3Type = andAll(for(j <- 0 until k) yield sum(zs.map((elem, i) => elem * intConst(s"${i},${j}"))) <= b)

      val (sol, z) = solve(partitionSetConstraints(sl, k) && cst, str)

      val zsk: Seq[(Int, Int)] = sl.flatMap(List.fill(k)(_)).zipWithIndex
      val res: Option[Seq[MultiSet[Int]]] = 
        toInt(sol).map( some => 
          for(j <- 0 until k)
            yield MultiSetFactory.from(some.zip(zsk).filter((x, p) => x > 0 && p._2 % k == j).map((x, p) => p._1))
        )
      z.delete()
      res
  private def knapsackConstraints(items: Seq[(Int, Int)], w: Int, v: Int): Z3Type =
    val zi: Seq[((Int, Int), Int)] = items.zipWithIndex
    val str: Seq[String] = Range(0, items.size).map(_.toString)
    val vars: Seq[Z3Type] = intConst(str)
    val cst1: Z3Type = vars >= 0
    val cst2: Z3Type = sum(zi.map((it, j) => intConst(j.toString) * it._1)) <= w
    val cst3: Z3Type = sum(zi.map((it, j) => intConst(j.toString) * it._2)) >= v
    cst1 && cst2 && cst3

  def boundedKnapsack(items: Seq[(Int, Int)], w: Int, v: Int, c: Int): Option[Seq[Int]] =
    val str: Seq[String] = Range(0, items.size).map(_.toString)
    val (sol, z) = solve(knapsackConstraints(items, w, v) && (intConst(str) <= c), str)
    z.delete()
    toInt(sol)


  def knapsack(items: Seq[(Int, Int)], w: Int, v: Int): Option[Seq[Int]] = boundedKnapsack(items, w, v, 1)

  def unboundedKnapsack(items: Seq[(Int, Int)], w: Int, v: Int): Option[Seq[Int]] =
    val str: Seq[String] = Range(0, items.size).map(_.toString)
    val (sol, z) = solve(knapsackConstraints(items, w, v), str)
    z.delete()
    toInt(sol)

}