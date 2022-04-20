package satapps

import scala.collection.immutable.Queue
import BooleanMatricesOps.{*, given}
import Extensions.*

type Vertex = Int
type Edge = (Vertex, Vertex)

class Graph private (val adjMat: Matrix[Boolean], val adjList: Map[Vertex, Set[Vertex]], val edgeSet: Set[Edge], val vertexSet: Set[Vertex], val wMat: Matrix[Int], val wAdjList: Map[Vertex, Set[(Vertex, Int)]], val wMap: Map[Edge, Int]){

  def this(v: Set[Vertex], e: Set[Edge]) =
    this(e.foldLeft(BoolMatrix.falses(v.size, v.size))((acc: Matrix[Boolean], e: Edge) => acc.updated(e._1, e._2, true)), 
    e.foldLeft(v.map((_, Set())).toMap)((m: Map[Vertex, Set[Vertex]], p: Edge) => 
      m + (p._1 -> (m(p._1) + p._2)) ), 
    e, 
    v,
    e.foldLeft(IntMatrix.zeros(v.size, v.size))((acc: Matrix[Int], e: Edge) => acc.updated(e._1, e._2, 1)),
    e.foldLeft(v.map((_, Set())).toMap)((m: Map[Vertex, Set[(Vertex, Int)]], p: Edge) => 
      m + (p._1 -> (m(p._1) + ((p._2, 1)))) ),
    e.map((_, 1)).toMap)

  def this(wMat: Matrix[Int]) =
    this(Matrix(wMat.unravel.map(_ > 0), wMat.r, wMat.c), 
    (for(i <- 0 until wMat.r) yield (i, (for(j <- 0 until wMat.c if wMat(i, j) > 0) yield j).toSet)).toMap, 
    (for(i <- 0 until wMat.r; j <- 0 until wMat.c if wMat(i, j) > 0) yield (i, j)).toSet, 
    Range(0,wMat.r).toSet,
    wMat,
    (for(i <- 0 until wMat.r) yield (i, (for(j <- 0 until wMat.c if wMat(i, j) > 0) yield (j, wMat(i, j))).toSet)).toMap,
    (for(i <- 0 until wMat.r; j <- 0 until wMat.c if wMat(i, j) > 0) yield ((i, j), wMat(i, j))).toMap)
    
  def this(v: Set[Vertex], e: Map[Edge, Int]) =
    this(e.keySet.foldLeft(BoolMatrix.falses(v.size, v.size))((acc: Matrix[Boolean], e: Edge) => acc.updated(e._1, e._2, true)), 
    e.keySet.foldLeft(v.map((_, Set())).toMap)((m: Map[Vertex, Set[Vertex]], p: Edge) => m + (p._1 -> (m(p._1) + p._2))), 
    e.keySet, 
    v,
    e.foldLeft(IntMatrix.zeros(v.size, v.size))((acc: Matrix[Int], p: (Edge, Int)) => acc.updated(p._1._1, p._1._2, p._2)),
    e.foldLeft(v.map((_, Set())).toMap)((m: Map[Vertex, Set[(Vertex, Int)]], p: (Edge, Int)) => 
      m + (p._1._1 -> (m(p._1._1) + ((p._1._2, p._2))))),
    e)
  
  lazy val incEdges: Map[Vertex, Set[Vertex]] = edgeSet.foldLeft(vertexSet.map((_, Set())).toMap)((m: Map[Vertex, Set[Vertex]], p: Edge) => 
      m + (p._2 -> (m(p._2) + p._1)) )

  def complement = Graph(adjMat.complement)
  def nonReflComplement = Graph((adjMat || BoolMatrix.id(adjMat.r)).complement)
  def transClos: Graph = Graph(adjMat.transClos())
  def undirected: Graph = Graph(adjMat)

  def bfs(source: Vertex): Map[Vertex, Int] = 
    def iter(dist: Map[Vertex, Int], queue: Queue[Vertex]): Map[Vertex, Int] =
      if (dist.keys == vertexSet)
        dist
      else
        val (e, q): (Vertex, Queue[Vertex]) = queue.dequeue
        val l = adjList(e).filter(!dist.contains(_))
        iter(dist ++ l.map(_ -> (dist(e) + 1)), q enqueueAll l)
    iter(Map(source -> 0), Queue(source))
  
}


object Graph {
  def empty(n: Int) = Graph(BoolMatrix.falses(n, n))
  def complete(n: Int) = empty(n).nonReflComplement
  def identity(n: Int) = Graph(BoolMatrix.id(n))
}
