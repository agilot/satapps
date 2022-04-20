package satapps

import java.util
import scala.collection.{IterableOps, IterableFactory, IterableFactoryDefaults, StrictOptimizedIterableOps}
import scala.collection.mutable.{Builder, ImmutableBuilder}

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
