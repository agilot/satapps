package satapps

import scala.collection.immutable.Queue
import satapps.Prop._
import java.awt.event.AdjustmentListener
import satapps.Graphs.GraphImpl

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
  
  def graphColoring(c: Int, solv: SATSolver): Boolean =
    val (env, res) = CNFSAT.solveSAT(andAll(vertexSet.toList.flatMap((k: Vertex) => 
      exactlyOne(Range(0, c).toList.map(i => Variable(s"x${i},${k}"))) :: 
      Range(0, c).toList.flatMap((i: Int) => adjList(k).map((m: Vertex) => Not(And(Variable(s"x${i},${k}"), Variable(s"x${i},${m}"))))))).toCNF(), solv)
      res == SAT
  
  def clique(k: Int, solv: SATSolver): Boolean =
    require(k >= 0)
    val n = adjList.size;
    if (k > n) false
    else 
      val c1 = andAll(
      (for(i <- 0 until k; j <- 0 until k; u <- 0 until n if i != j)
        yield orAll(Not(Variable(s"x${i},${u}")) :: (adjList(u) - u).map(v => Variable(s"x${j},${v}")).toList)).toList)
      val c2 = andAll((for(i <- 0 until k) yield
        exactlyOne((for(u <- 0 until n)
          yield Variable(s"x${i},${u}")).toList)).toList)
      val (env, res) =CNFSAT.solveSAT(And(c1, c2), solv)
      res == SAT
  
  def vertexCover(k: Int, solv: SATSolver): Boolean =
    val vars = vertexSet.map(v => Variable(s"x${v}"))
    //val exp = And(atMostK(vars, k, "r1"), And(andAll(edgeSet.map((u, v) => Variable(s"x${u}${v}"))), andAll(for(p <- adjList if p._2 != Set()) yield Prop.implies(Variable(s"x${p._1}"), andAll(p._2.map(v => Variable(s"x${p._1}${v}")))))))
    val exp = And(atMostK(vars, k, "r1"), andAll(edgeSet.map((u, v) => And(Variable(s"e${u},${v}"), Prop.implies(Variable(s"e${u},${v}"), Or(Variable(s"x${u}"), Variable(s"x${v}")))))))
    println(exp)
    val (env, res) = CNFSAT.solveSAT(exp, solv)
    res == SAT
  
  def dominatingSet(k: Int, solv: SATSolver): Boolean =
    val vars = vertexSet.map(v => Variable(s"x${v}")).toList
    val vert = vertexSet.map(v => Variable(s"v${v}")).toList
    val exp = And(atMostK(vars, k), And(andAll(vert), andAll(vertexSet.map(v => Prop.implies(Variable(s"v${v}"), Or(Variable(s"x${v}"), orAll(adjList(v).map(v2 => Variable(s"x${v2}")))))))))
    val (env, res) = CNFSAT.solveSAT(exp, solv)
    res == SAT

  def complement: Graph

  def indset(k: Int, solv: SATSolver) : Boolean = 
    complement.clique(k, solv)
}

class GraphFromMatrix(mat: BinaryMatrix) extends Graph{
    override lazy val adjMat = mat
    override lazy val vertexSet: Set[Vertex] = Range(0,mat.rows).toSet
    override lazy val adjList = (for(i <- 0 until mat.rows) yield (i, (for(j <- 0 until mat.cols if mat(i, j)) yield j).toSet)).toMap
    override lazy val edgeSet = (for(i <- 0 until mat.rows; j <- 0 until mat.cols if mat(i, j)) yield (i, j)).toSet

    def complement = GraphFromMatrix(mat.complement)
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
