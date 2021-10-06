package satapps

import scala.collection.immutable.Queue
import satapps.Prop._

type Vertex = Int
type Edge = (Vertex, Vertex)

abstract class Graph{
  lazy val adjMat: BinaryMatrix
  lazy val adjList: Map[Vertex, List[Vertex]]
  lazy val edgeSet: Set[Edge]
  lazy val vertexSet: Set[(Vertex)]

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
  
  def graphColoring(c: Int, solv: SATSolver): Boolean =
    println(andAll(vertexSet.toList.flatMap((k: Vertex) => 
      exactlyOne(Range(0, c).toList.map(i => Variable(s"x${i}${k}"))) :: 
      Range(0, c).toList.flatMap((i: Int) => adjList(k).map((m: Vertex) => Not(And(Variable(s"x${i}${k}"), Variable(s"x${i}${m}"))))))).toCNF.varSet().size)
    val (env, res) = CNFSAT.solveSAT(andAll(vertexSet.toList.flatMap((k: Vertex) => 
      exactlyOne(Range(0, c).toList.map(i => Variable(s"x${i}${k}"))) :: 
      Range(0, c).toList.flatMap((i: Int) => adjList(k).map((m: Vertex) => Not(And(Variable(s"x${i}${k}"), Variable(s"x${i}${m}"))))))).toCNF, solv)
      println(env)
      res == SAT
    
}

class GraphFromMatrix(mat: BinaryMatrix) extends Graph{
    override lazy val adjMat = mat
    override lazy val vertexSet: Set[Vertex] = Range(0,mat.r).toSet
    override lazy val adjList = (for(i <- 0 until mat.r) yield (i, (for(j <- 0 until mat.c if mat(i, j)) yield j).toList)).toMap
    override lazy val edgeSet = (for(i <- 0 until mat.r; j <- 0 until mat.c if mat(i, j)) yield (i, j)).toSet
}

class GraphFromEdgeSet(v: Set[Vertex], e: Set[Edge]) extends Graph{
    override lazy val adjMat = buildMatrix(edgeSet.toList)
    override lazy val vertexSet: Set[Vertex] = v
    override lazy val adjList = e.toList.foldLeft(v.map((_, Nil)).toMap)((m: Map[Vertex, List[Vertex]], p: Edge) => 
      m + (p._1 -> (p._2 :: m(p._1))) )
    override lazy val edgeSet = e

    private def buildMatrix(l: List[Edge]): BinaryImMatrix =
      l.foldLeft(Mat.imZeros(vertexSet.size, vertexSet.size))((acc: BinaryImMatrix, e: Edge) => acc.set(e._1, e._2, true))
}