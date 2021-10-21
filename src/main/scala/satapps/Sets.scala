package satapps

import java.util
import scala.collection.{IterableOps, IterableFactory, IterableFactoryDefaults, StrictOptimizedIterableOps}
import scala.collection.mutable.{Builder, ImmutableBuilder}

trait MultiSet[T] extends (T => Int) 
  with Iterable[T] 
  with IterableOps[T, MultiSet, MultiSet[T]]
  with IterableFactoryDefaults[T, MultiSet]
  with StrictOptimizedIterableOps[T, MultiSet, MultiSet[T]]{

  def incl(elem: T) : MultiSet[T]
  def inclN(elem: T, n: Int): MultiSet[T] = Range(0, n).foldLeft(this)((s, i) => s.incl(elem))
  def excl(elem: T) : MultiSet[T]
  def exclN(elem: T, n: Int): MultiSet[T] = Range(0, n).foldLeft(this)((s, i) => s.excl(elem))
  def mult(elem: T) : Int

  override def toString(): String = 
    if (size == 0) "()"
    else 
      "(" + head.toString + tail.foldLeft("")((s: String, e : T) => s + ", " + e.toString()) + ")"
  
  def intersect(set: MultiSet[T]) : MultiSet[T] = 
    val newS = set.filter(contains(_))
    foldLeft(newS)((acc, e) => if (acc(e) > mult(e)) acc - e else acc)

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
}

object MultiSetFactory extends IterableFactory[MultiSet] {

  def from[T](source: IterableOnce[T]): MultiSet[T] =
    (newBuilder[T] ++= source).result()

  def empty[T]: MultiSet[T] = ImMultiSet(Map())

  def newBuilder[A]: Builder[A, MultiSet[A]] =
    new ImmutableBuilder[A, MultiSet[A]](empty) {
      def addOne(elem: A): this.type = { elems = elems.incl(elem); this }
    }
}

class ImMultiSet[T](private val m: Map[T, Int]) extends MultiSet[T]{

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
      case set: ImMultiSet[_] => m == set.m
      case _ => false
    }
  override def incl(elem: T) = 
    ImMultiSet(m.updated(elem, mult(elem) + 1))

  override def excl(elem: T) = 
    m.get(elem) match{
      case None => ImMultiSet(m)
      case Some(1) => ImMultiSet(m - elem)
      case Some(i) => ImMultiSet(m.updated(elem, i - 1))
    }
  
  override def mult(elem: T) = m.get(elem).getOrElse(0)
  
  override def intersect(set: MultiSet[T]) = ImMultiSet(m.view.filterKeys(set.contains(_)).toMap.map((k, v) => k -> math.min(v, set(k))))
}

object SetRed{

  def setPacking[T](k: Int, c: Set[Set[T]], solv: SATSolver): Boolean =
    val n = c.size
    val z = c.zip(Range(0, n))
    val g = GraphFromEdgeSet(Range(0, n).toSet, (for(p1 <- z; p2 <- z; if (p1._2 != p2._2) && ((p1._1 & p2._1) != Set()))
      yield (p1._2, p2._2)).toSet)
    println(g.edgeSet)
    g.indset(k, solv)


}

