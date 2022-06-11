package satapps

import scala.collection.immutable.Queue
import scala.annotation.targetName
import BooleanMatricesOps.{*, given}
import Extensions.*
import problems.Graphs.*

type Vertex = Int
type Edge = (Vertex, Vertex)

trait Graph {
  def adjMat: Matrix[Boolean]
  def adjList: Map[Vertex, Set[Vertex]]
  def edgeSet: Set[Edge]
  def vertexSet: Set[Vertex]
  def wMat: Matrix[Int]
  def wAdjList: Map[Vertex, Set[(Vertex, Int)]]
  def wMap: Map[Edge, Int]

  lazy val inNeighb: Map[Vertex, Set[Vertex]] = edgeSet.foldLeft(vertexSet.map((_, Set())).toMap)((m: Map[Vertex, Set[Vertex]], p: Edge) => 
    m + (p._2 -> (m(p._2) + p._1))
  )

  def outNeighb: Map[Vertex, Set[Vertex]] = adjList

  lazy val neighb: Map[Vertex, Set[Vertex]] = inNeighb.map((v, s) => (v, s ++ adjList(v)))
 
  lazy val outIncidence: Map[Vertex, Set[Edge]] = edgeSet.foldLeft(vertexSet.map((_, Set())).toMap)((m: Map[Vertex, Set[Edge]], p: Edge) => 
    m + (p._1 -> (m(p._1) + p)))
  lazy val inIncidence: Map[Vertex, Set[Edge]] = edgeSet.foldLeft(vertexSet.map((_, Set())).toMap)((m: Map[Vertex, Set[Edge]], p: Edge) => 
    m + (p._2 -> (m(p._2) + p)))
  lazy val incidence: Map[Vertex, Set[Edge]] = inIncidence.map((v, s) => (v, s ++ outIncidence(v)))
  
  def neighb(v: Set[Vertex]): Set[Vertex] = v.foldLeft(Set[Vertex]())(_ ++ neighb(_)) -- v


  def complement: Graph = Graph(adjMat.complement)
  def nonReflComplement: Graph = Graph((adjMat || BoolMatrix.id(adjMat.rows)).complement)
  def transClos: Graph = Graph(adjMat.transClos())
  def reversed: Graph = Graph(vertexSet, edgeSet.map((i, j) => (j, i)))
  def unweighted: Graph = Graph(adjMat)
  def undirected(doubleEdges: Boolean = true): Graph =
    val revEs = reversed.edgeSet
    if (doubleEdges) 
      Graph(vertexSet, edgeSet ++ revEs)
    else
      Graph(vertexSet, edgeSet ++ revEs -- (for(i <- 0 until vertexSet.size; j <- i + 1 until vertexSet.size) yield (i, j)))

  def connected: Boolean = bfs(0).size == vertexSet.size
  def isClique: Boolean = undirected(true).edgeSet.size == vertexSet.size * (vertexSet.size - 1) / 2
  def isIndependent: Boolean = undirected(true).edgeSet.size == 0


  def induced(vertices: Set[Vertex]): Graph = 
    Graph(vertices, edgeSet.filter(vertices(_) && vertices(_)))

  def bfs(source: Vertex): Map[Vertex, Int] = 
    def iter(dist: Map[Vertex, Int], queue: Queue[Vertex]): Map[Vertex, Int] =
      if (dist.keys == vertexSet)
        dist
      else
        val (e, q): (Vertex, Queue[Vertex]) = queue.dequeue
        val l = adjList(e).filter(!dist.contains(_))
        iter(dist ++ l.map(_ -> (dist(e) + 1)), q enqueueAll l)
    iter(Map(source -> 0), Queue(source))
  
  /****Numbers*****/

  def independenceNumber: Option[Int] = Indset.max(this).map(_.size)
  def vertexCoverNumber: Option[Int] = VertexCover.min(this).map(_.size)
  def cliqueNumber: Option[Int] = Clique.max(this).map(_.size)
  def cliqueCoverNumber: Option[Int] = CliqueCover.min(this).map(_.size)
  def chromaticNumber: Option[Int] = Coloring.min(this).map(_.values.size)  
  def edgeChromaticNumber: Option[Int] = EdgeColoring.min(this).map(_.values.size)
  def dominationNumber: Option[Int] = DominatingSet.min(this).map(_.size)
  def domaticNumber: Option[Int] = DomaticPartition.max(this).map(_.size)
  def totalDominationNumber: Option[Int] = try{ Some(TotalDominatingSet.min(this).size)}
    catch{
      case e: IllegalArgumentException => None
    }
  def connectedDominationNumber: Option[Int] =  try{ Some(ConnectedDominatingSet.min(this).size)}
    catch{
      case e: IllegalArgumentException => None
    }
  def independentDominationNumber: Int = IndependentDominatingSet.min(this).size

}

class SetGraph (override val vertexSet: Set[Vertex], override val edgeSet: Set[Edge]) extends Graph {
  override lazy val adjMat: Matrix[Boolean] = 
    edgeSet.foldLeft(BoolMatrix.falses(vertexSet.size, vertexSet.size))((acc: Matrix[Boolean], e: Edge) => acc.updated(e._1, e._2, true))

  override lazy val adjList: Map[Vertex, Set[Vertex]] = 
    edgeSet.foldLeft(vertexSet.map((_, Set())).toMap)((m: Map[Vertex, Set[Vertex]], p: Edge) => 
      m + (p._1 -> (m(p._1) + p._2)) 
    )
  
  override lazy val wMat: Matrix[Int] = 
    edgeSet.foldLeft(IntMatrix.zeros(vertexSet.size, vertexSet.size))((acc: Matrix[Int], e: Edge) => acc.updated(e._1, e._2, 1))

  override lazy val wAdjList: Map[Vertex, Set[(Vertex, Int)]] = 
    edgeSet.foldLeft(vertexSet.map((_, Set())).toMap)((m: Map[Vertex, Set[(Vertex, Int)]], p: Edge) => 
      m + (p._1 -> (m(p._1) + ((p._2, 1)))) 
    )

  override lazy val wMap: Map[Edge, Int] =
    edgeSet.map((_, 1)).toMap
}

class WeightedSetGraph (override val vertexSet: Set[Vertex], override val wMap: Map[Edge, Int]) extends Graph {
  override lazy val adjMat: Matrix[Boolean] = 
    wMap.keySet.foldLeft(BoolMatrix.falses(vertexSet.size, vertexSet.size))((acc: Matrix[Boolean], e: Edge) => acc.updated(e._1, e._2, true))

  override lazy val adjList: Map[Vertex, Set[Vertex]] =
    wMap.keySet.foldLeft(vertexSet.map((_, Set())).toMap)((m: Map[Vertex, Set[Vertex]], p: Edge) => m + (p._1 -> (m(p._1) + p._2)))

  override lazy val edgeSet: Set[Edge] =
    wMap.keySet

  override lazy val wMat: Matrix[Int] =
    wMap.foldLeft(IntMatrix.zeros(vertexSet.size, vertexSet.size))((acc: Matrix[Int], p: (Edge, Int)) => acc.updated(p._1._1, p._1._2, p._2))

  override lazy val wAdjList: Map[Vertex, Set[(Vertex, Int)]] =
    wMap.foldLeft(vertexSet.map((_, Set())).toMap)((m: Map[Vertex, Set[(Vertex, Int)]], p: (Edge, Int)) => 
      m + (p._1._1 -> (m(p._1._1) + ((p._1._2, p._2))))
    )
}

class MatrixGraph (override val wMat: Matrix[Int]) extends Graph {
  override lazy val adjMat: Matrix[Boolean] =
    Matrix(wMat.unravel.map(_ > 0), wMat.rows, wMat.columns)

  override lazy val adjList: Map[Vertex, Set[Vertex]] =
    (for(i <- 0 until wMat.rows) yield (i, (for(j <- 0 until wMat.columns if wMat(i, j) > 0) yield j).toSet)).toMap

  override lazy val edgeSet: Set[Edge] = 
    (for(i <- 0 until wMat.rows; j <- 0 until wMat.columns if wMat(i, j) > 0) yield (i, j)).toSet

  override lazy val vertexSet: Set[Vertex] =
    Range(0,wMat.rows).toSet

  override lazy val wAdjList: Map[Vertex, Set[(Vertex, Int)]] =
    (for(i <- 0 until wMat.rows) yield (i, (for(j <- 0 until wMat.columns if wMat(i, j) > 0) yield (j, wMat(i, j))).toSet)).toMap

  override lazy val wMap: Map[Edge, Int] =
    (for(i <- 0 until wMat.rows; j <- 0 until wMat.columns if wMat(i, j) > 0) yield ((i, j), wMat(i, j))).toMap
}

object Graph {
  def apply(v: Set[Vertex], e: Set[Edge]): Graph = SetGraph(v, e)
  def apply(wMat: Matrix[Int]): Graph = MatrixGraph(wMat)
  def apply(v: Set[Vertex], e: Map[Edge, Int]): Graph = WeightedSetGraph(v, e)

  def empty(n: Int): Graph = Graph(BoolMatrix.falses(n, n))
  def complete(n: Int): Graph = empty(n).nonReflComplement
  def identity(n: Int): Graph = Graph(BoolMatrix.id(n))
}
