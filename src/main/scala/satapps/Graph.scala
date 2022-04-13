package satapps

import scala.collection.immutable.Queue
import Z3.{|| as _, *}
import BooleanMatricesOps.*

type Vertex = Int
type Edge = (Vertex, Vertex)

class Graph (val adjMat: Matrix[Boolean], val adjList: Map[Vertex, Set[Vertex]], val edgeSet: Set[Edge], val vertexSet: Set[Vertex]){

  def this(mat: Matrix[Boolean]) =
    this(mat, 
    (for(i <- 0 until mat.r) yield (i, (for(j <- 0 until mat.c if mat(i, j)) yield j).toSet)).toMap, 
    (for(i <- 0 until mat.r; j <- 0 until mat.c if mat(i, j)) yield (i, j)).toSet, 
    Range(0,mat.r).toSet)
    
  def this(v: Set[Vertex], e: Set[Edge]) =
    this(e.foldLeft(Mat.zeros(v.size, v.size))((acc: Matrix[Boolean], e: Edge) => acc.updated(e._1, e._2, true)), 
    e.foldLeft(v.map((_, Set())).toMap)((m: Map[Vertex, Set[Vertex]], p: Edge) => 
      m + (p._1 -> (m(p._1) + p._2)) ), 
    e, 
    v)
  
  lazy val incEdges: Map[Vertex, Set[Vertex]] = edgeSet.foldLeft(vertexSet.map((_, Set())).toMap)((m: Map[Vertex, Set[Vertex]], p: Edge) => 
      m + (p._2 -> (m(p._2) + p._1)) )

  def complement = Graph(adjMat.complement)
  def nonReflComplement = Graph((adjMat || Mat.id(adjMat.r)).complement)
  def transClos: Graph = Graph(adjMat.transClos())

  def bfs(source: Vertex): Map[Vertex, Int] = 
      def iter(dist: Map[Vertex, Int], queue: Queue[Vertex]): Map[Vertex, Int] =
        if (dist.keys == vertexSet)
          dist
        else
          val (e, q): (Vertex, Queue[Vertex]) = queue.dequeue
          val l = adjList(e).filter(!dist.contains(_))
          iter(dist ++ l.map(_ -> (dist(e) + 1)), q enqueueAll l)
      iter(Map(source -> 0), Queue(source))
  
  def coloring(c: Int): Option[Seq[Int]] =
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
    
  def hamiltonianCycle: Option[Seq[Edge]] =
    val esl: Seq[Edge] = edgeSet.toList
    val str: Seq[String] = esl.map((v1, v2) => s"${v1},${v2}")
    val vars: Seq[Z3Type] = intConst(str)
    val cst1: Z3Type = andAll(adjList.map((v1, se) => sum(se.map(v2 => intConst(s"${v1},${v2}")).toList) === 1).toList)
    val cst2: Z3Type = andAll(incEdges.map((v2, se) => sum(se.map(v1 => intConst(s"${v1},${v2}")).toList) === 1).toList)
    val cst3: Z3Type = andAll(edgeSet.map((v1, v2) => (intConst(s"${v1},${v2}") + intConst(s"${v2},${v1}")) <= 1).toList)
    val cst4: Z3Type = vars >= 0 && vars <= 1
    val cst5: Z3Type = sum(vars) === vertexSet.size

    val (sol, z) = solve(cst1 && cst2 && cst3 && cst4 && cst5, str)
    val res = toInt(sol).map(some => some.zip(esl).filter((v, e) => v > 0).map((v, e) => e))
    z.delete()
    res
  
  def hamiltonianPath: Option[Seq[Edge]] =
    val n: Int = vertexSet.size
    val nG: Graph = Graph(Mat.fromBlock(adjMat, Mat.ones(n, 1), Mat.ones(1, n), Mat.zeros(1, 1)))
    val p = nG.hamiltonianCycle.map(_.filter(p => p._1 < n && p._2 < n))
    p.map(some => if(some.size == n) some.tail else some)
  
  def dominatingSet(k: Int): Option[Set[Vertex]] =
    val str: Seq[String] = Range(0, vertexSet.size).map(_.toString)
    val vars: Seq[Z3Type] = intConst(str)
    val cst1: Z3Type = andAll((for (v1 <- 0 until vertexSet.size) yield sum(intConst((adjList(v1) + v1).map(_.toString).toList)) >= 1).toList)
    val cst2: Z3Type = vars >= 0 && sum(vars) <= k
    
    val (sol, z) = solve(cst1 && cst2, str)
    val res = filterSol(sol).map(_.toSet)
    z.delete()
    res

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


object Graphs{
  def empty(n: Int) = Graph(Mat.zeros(n, n))
  def complete(n: Int) = empty(n).nonReflComplement
  def identity(n: Int) = Graph(Mat.id(n))
}
