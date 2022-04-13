package satapps

import java.util
import scala.collection.{IterableOps, IterableFactory, IterableFactoryDefaults, StrictOptimizedIterableOps}
import scala.collection.mutable.{Builder, ImmutableBuilder}

import Z3.*

class MultiSet[T] private (m: Map[T, Int]) extends (T => Int) 
  with Iterable[T] 
  with IterableOps[T, MultiSet, MultiSet[T]]
  with IterableFactoryDefaults[T, MultiSet]
  with StrictOptimizedIterableOps[T, MultiSet, MultiSet[T]]{

  private lazy val map: Map[T, Int] = m
  
  def this(m: (T, Int)*) = this(m.toMap)
  def this() = this(Map()) 

  def incl(elem: T) = MultiSet(m.updated(elem, mult(elem) + 1))
  def inclN(elem: T, n: Int): MultiSet[T] = Range(0, n).foldLeft(this)((s, i) => s.incl(elem))
  def excl(elem: T) = 
    m.get(elem) match{
      case None => MultiSet(m)
      case Some(1) => MultiSet(m - elem)
      case Some(i) => MultiSet(m.updated(elem, i - 1))
    }
  def exclN(elem: T, n: Int): MultiSet[T] = Range(0, n).foldLeft(this)((s, i) => s.excl(elem))
  def mult(elem: T) = m.get(elem).getOrElse(0)

  override def toString(): String = 
    if (size == 0) "()"
    else 
      "(" + head.toString + tail.foldLeft("")((s: String, e : T) => s + ", " + e.toString()) + ")"
  
  def intersect(set: MultiSet[T]) = MultiSet(m.view.filterKeys(set.contains(_)).toMap.map((k, v) => k -> math.min(v, set(k))))

  def removedAll(it: Iterable[T]): MultiSet[T] = it.foldLeft(this)(_ - _)
  def diff(set: MultiSet[T]): MultiSet[T] = removedAll(set)
  def union(set: MultiSet[T]): MultiSet[T] = (this -- set) ++ (set -- this) ++ (set & this)

  override val iterableFactory: IterableFactory[MultiSet] = MultiSetFactory

  def +(elem: T) = incl(elem)
  def -(elem: T) = excl(elem)
  def --(it: Iterable[T]) = removedAll(it)
  def &(set: MultiSet[T]) = intersect(set)
  def &~(set:MultiSet[T]) = diff(set)

  def apply(elem: T): Int = mult(elem)
  def sum(set: MultiSet[T]) : MultiSet[T] = concat(set)
  def contains(elem: T) : Boolean = mult(elem) > 0


  override def iterator: Iterator[T] = new Iterator[T]{
    val i: Iterator[(T, Int)] = m.iterator
    var pair: Option[(T, Int)] = optNext
    private def optNext = if (i.hasNext) Some(i.next) else None
    def hasNext: Boolean = pair.isDefined
    def next(): T = pair match{
      case None => throw java.util.NoSuchElementException()
      case Some(p) => 
        val e = p._1
        pair =  if (p._2 == 1) optNext else Some((p._1, p._2 - 1))
        e
    }
  }

    override def equals(that: Any): Boolean = 
    that match{
      case set: MultiSet[_] => m == set.map
      case _ => false
    }
}

object MultiSetFactory extends IterableFactory[MultiSet] {

  def from[T](source: IterableOnce[T]): MultiSet[T] =
    (newBuilder[T] ++= source).result()

  def empty[T]: MultiSet[T] = MultiSet()

  def newBuilder[A]: Builder[A, MultiSet[A]] =
    new ImmutableBuilder[A, MultiSet[A]](empty) {
      def addOne(elem: A): this.type = { elems = elems.incl(elem); this }
    }
}

object SetRed{

  def setPacking[T](k: Int, c: Seq[Set[T]]): Option[Set[Int]] =
    val z = c.zipWithIndex
    val g = Graph(Range(0, c.size).toSet, (for(p1 <- z; p2 <- z; if (p1._2 != p2._2) && ((p1._1 & p2._1) != Set()))
      yield (p1._2, p2._2)).toSet)
    g.indset(k)

  def setCover[T](k: Int, u: Set[T], c: Seq[Set[T]]): Option[Set[Int]] =
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
    
  def partition(s: MultiSet[Int]): Option[(MultiSet[Int], MultiSet[Int])] =
    multiwayPartitioning(s, 2).map(some => (some.head, some.tail.head))
  

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
    nPartition(s, 3).map(_.map( m =>
      val l: List[Int] = m.toList
      val tl = l.tail
      (l.head, tl.head, tl.tail.head)
    ))
  
  def nPartition(s: MultiSet[Int], n: Int): Option[Seq[MultiSet[Int]]] =
    if (s.size % n == 0)
      val tot: Int = s.reduce(_ + _)
      val k = s.size/n
      if(tot % k == 0)
        val sl: Seq[Int] = s.toSeq
        val str: Seq[String] = for(i <- 0 until s.size; j <- 0 until k) yield s"${i},${j}"
        val cst: Z3Type = andAll(for(j <- 0 until k) yield sum(for(i <- 0 until s.size) yield intConst(s"${i},${j}")) === n)
        val (sol, z) = solve(partitionConstraints(sl, k) && cst, str)
        
        val zsk: Seq[(Int, Int)] = sl.flatMap(List.fill(k)(_)).zipWithIndex
        val res: Option[Seq[MultiSet[Int]]] = 
          toInt(sol).map( some => 
            for(j <- 0 until k)
              yield MultiSetFactory.from(some.zip(zsk).filter((x, p) => x > 0 && p._2 % k == j).map((x, p) => p._1))
          )
        z.delete()
        res
      else None
    else None
      

  def multiwayPartitioning(s: MultiSet[Int], k: Int): Option[Seq[MultiSet[Int]]] =
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

  def boundedKnapsack(items: Seq[(Int, Int)], w: Int, v: Int): Option[Seq[Int]] =
    val str: Seq[String] = Range(0, items.size).map(_.toString)
    val (sol, z) = solve(knapsackConstraints(items, w, v), str)
    z.delete()
    toInt(sol)

}

