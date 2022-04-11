package satapps

import scala.collection.immutable.Queue
import java.awt.event.AdjustmentListener
import satapps.Graphs.GraphImpl
import z3.scala.*

type Vertex = Int
type Edge = (Vertex, Vertex)

abstract class Graph{
  lazy val adjMat: BinaryMatrix
  lazy val adjList: Map[Vertex, Set[Vertex]]
  lazy val edgeSet: Set[Edge]
  lazy val vertexSet: Set[Vertex]

  def transClos() = 
    GraphFromMatrix(adjMat.transClos())

  def bfs(source: Vertex): Map[Vertex, Int] = 
      def iter(dist: Map[Vertex, Int], queue: Queue[Vertex]): Map[Vertex, Int] =
        if (dist.keys == vertexSet)
          dist
        else
          val (e, q): (Vertex, Queue[Vertex]) = queue.dequeue
          val l = adjList(e).filter(!dist.contains(_))
          iter(dist ++ l.map(_ -> (dist(e) + 1)), q enqueueAll l)
      iter(Map(source -> 0), Queue(source))
  
  def graphColoring(c: Int): Option[Seq[Int]] =
    val str: Seq[String] = 
      for(i <- 0 until vertexSet.size; j <- 0 until c)
        yield s"${i},${j}"
    val vars: Seq[Z3Type] = intConst(str)
    val cst1: Z3Type = vars >= 0
    val cst2: Z3Type = andAll((for((v1, v2) <- edgeSet; i <- 0 until c) yield
      intConst(s"${v1},${i}") + intConst(s"${v2},${i}") <= 1).toList)
    val cst3: Z3Type = andAll((for(v <- 0 until vertexSet.size) yield sum(for(i <- 0 until c) yield intConst(s"${v},${i}")) === 1))
      
    val (sol, z) = solve(cst1 && cst2 && cst3, str)
    val res = toInt(sol).map(_.zipWithIndex.filter((cs, idx) => cs >= 1).map((cs, idx) => idx % c))
    z.delete()
    res

  def clique(k: Int): Option[Set[Int]] =
    require(k >= 0)
    nonReflComplement.indset(k)
  
  def vertexCover(k: Int): Option[Set[Vertex]] =
    val str: Seq[String] = Range(0, vertexSet.size).map(_.toString)
    val vars: Seq[Z3Type] = intConst(str)
    val cst1: Z3Type = andAll((for (v1, v2) <- edgeSet yield intConst(v1.toString) + intConst(v2.toString) >= 1).toList)
    val cst2: Z3Type = vars >= 0 && sum(vars) <= k

    val (sol, z) = solve(cst1 && cst2, str)
    val res = filterSol(sol).map(_.toSet)
    z.delete()
    res
    

  
  def dominatingSet(k: Int): Option[Set[Vertex]] =
    val str: Seq[String] = Range(0, vertexSet.size).map(_.toString)
    val vars: Seq[Z3Type] = intConst(str)
    val cst1: Z3Type = andAll((for (v1 <- 0 until vertexSet.size) yield sum(intConst((adjList(v1) + v1).map(_.toString).toList)) >= 1).toList)
    val cst2: Z3Type = vars >= 0 && sum(vars) <= k
    
    val (sol, z) = solve(cst1 && cst2, str)
    val res = filterSol(sol).map(_.toSet)
    z.delete()
    res

  def complement: Graph
  def nonReflComplement: Graph

  def indset(k: Int) : Option[Set[Int]] = 
  if (edgeSet.size > 0)
    val str: Seq[String] = Range(0, vertexSet.size).map(_.toString)
    val vars: Seq[Z3Type] = intConst(str)
    val cst1: Z3Type = andAll((for (v1, v2) <- edgeSet yield intConst(v1.toString) + intConst(v2.toString) <= 1).toList)
    val cst2: Z3Type = vars >= 0 && sum(vars) >= k

    val (sol, z) = solve(cst1 && cst2, str)
    val res = filterSol(sol).map(_.toSet)
    z.delete()
    res
  else if (vertexSet.size >= k) Some(Range(0, k).toSet) else None
}

class GraphFromMatrix(mat: BinaryMatrix) extends Graph{
    override lazy val adjMat = mat
    override lazy val vertexSet: Set[Vertex] = Range(0,mat.rows).toSet
    override lazy val adjList = (for(i <- 0 until mat.rows) yield (i, (for(j <- 0 until mat.cols if mat(i, j)) yield j).toSet)).toMap
    override lazy val edgeSet = (for(i <- 0 until mat.rows; j <- 0 until mat.cols if mat(i, j)) yield (i, j)).toSet

    def complement = GraphFromMatrix(mat.complement)
    def nonReflComplement = GraphFromMatrix((mat || Mat.imId(mat.rows)).complement)
  }

class GraphFromEdgeSet(v: Set[Vertex], e: Set[Edge]) extends Graph{
    override lazy val adjMat = buildMatrix(edgeSet.toList)
    override lazy val vertexSet: Set[Vertex] = v
    override lazy val adjList = e.foldLeft(v.map((_, Set())).toMap)((m: Map[Vertex, Set[Vertex]], p: Edge) => 
      m + (p._1 -> (m(p._1) + p._2)) )
    override lazy val edgeSet = e

    private def buildMatrix(l: List[Edge]): BinaryImMatrix =
      l.foldLeft(Mat.imZeros(vertexSet.size, vertexSet.size))((acc: BinaryImMatrix, e: Edge) => acc.updated(e._1, e._2, true))

    def complement = GraphFromEdgeSet(v, (for i <- v; j <- v yield (i, j)).toSet -- e)
    def nonReflComplement = GraphFromEdgeSet(v, (for i <- v; j <- v if i != j yield (i, j)).toSet -- e)
  }

object Graphs{
  abstract class GraphImpl
  case object FromAdjList extends GraphImpl
  case object FromAdjMat extends GraphImpl
  case object FromEdgeSet extends GraphImpl

  def vert(n: Int) = Range(0, n).toSet

  //CASE MISSING
  def empty(n: Int, impl: GraphImpl) = impl match{
    case FromEdgeSet => GraphFromEdgeSet(vert(n), Set())
    case FromAdjMat => GraphFromMatrix(Mat.imZeros(n, n))
  }

  //CASE MISSING
  def complete(n: Int, impl: GraphImpl) = impl match{
    case FromEdgeSet => GraphFromEdgeSet(vert(n), (for(i <- 0 until n; j <- 0 until n; if i != j) yield (i, j)).toSet)
  }
}
