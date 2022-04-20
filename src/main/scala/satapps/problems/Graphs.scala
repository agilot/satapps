package satapps.problems

import satapps.*
import Z3.{*, given}
import BooleanMatricesOps.{*, given}
import scala.collection.immutable.ArraySeq
import Extensions.*

object Graphs {

  def coloring(g: Graph)(c: Int): Option[Seq[Int]] =
    val str: Seq[String] = 
      for(i <- 0 until g.vertexSet.size; j <- 0 until c)
        yield s"${i},${j}"
    val vars: Seq[Z3Type] = intConst(str)
    val cst1: Z3Type = vars >= 0
    val cst2: Z3Type = andAll((for((v1, v2) <- g.edgeSet; i <- 0 until c) yield
      intConst(s"${v1},${i}") + intConst(s"${v2},${i}") <= 1).toList)
    val cst3: Z3Type = andAll((for(v <- 0 until g.vertexSet.size) yield sum(for(i <- 0 until c) yield intConst(s"${v},${i}")) === 1))

    val (sol, z) = solve(cst1 && cst2 && cst3, str)
    val res = toInt(sol).map(_.zipWithIndex.filter((cs, idx) => cs >= 1).map((cs, idx) => idx % c))
    z.delete()
    res

  def clique(g: Graph)(k: Int): Option[Set[Int]] =
    require(k >= 0)
    indset(g.nonReflComplement)(k)

  def cliquePartition(g: Graph)(k: Int): Option[Seq[Set[Int]]] =
    coloring(g.nonReflComplement)(k).map(_.zipWithIndex.foldLeft(ArraySeq.fill(k)(Set(): Set[Vertex]))((acc, p) => acc.updated(p._1, acc(p._1) + p._2)))

  def vertexCover(g: Graph)(k: Int): Option[Set[Vertex]] =
    val str: Seq[String] = Range(0, g.vertexSet.size).map(_.toString)
    val vars: Seq[Z3Type] = intConst(str)
    val cst1: Z3Type = andAll((for (v1, v2) <- g.edgeSet yield intConst(v1.toString) + intConst(v2.toString) >= 1).toList)
    val cst2: Z3Type = vars >= 0 && sum(vars) <= k

    val (sol, z) = solve(cst1 && cst2, str)
    val res = filterSol(sol).map(_.toSet)
    z.delete()
    res

  def hamiltonianCycle(g: Graph): Option[Seq[Edge]] =
    travelingSalesman(g.undirected)(g.vertexSet.size)

  def travelingSalesman(g: Graph)(d: Int): Option[Seq[Edge]] =
    val esl: Seq[Edge] = g.edgeSet.toList
    val str: Seq[String] = esl.map((v1, v2) => s"${v1},${v2}")
    val vars: Seq[Z3Type] = intConst(str)
    val cst1: Z3Type = andAll(g.adjList.map((v1, se) => sum(se.map(v2 => intConst(s"${v1},${v2}")).toList) === 1).toList)
    val cst2: Z3Type = andAll(g.incEdges.map((v2, se) => sum(se.map(v1 => intConst(s"${v1},${v2}")).toList) === 1).toList)
    val cst3: Z3Type = andAll(g.edgeSet.map((v1, v2) => (intConst(s"${v1},${v2}") + intConst(s"${v2},${v1}")) <= 1).toList)
    val cst4: Z3Type = vars >= 0 && vars <= 1
    val cst5: Z3Type = sum(vars) === g.vertexSet.size
    val cst6: Z3Type = sum(esl.map(e => intConst(s"${e._1}, ${e._2}") * g.wMap(e))) <= d

    val (sol, z) = solve(cst1 && cst2 && cst3 && cst4 && cst5 && cst6, str)
    val res = toInt(sol).map(some => some.zip(esl).filter((v, e) => v > 0).map((v, e) => e))
    z.delete()
    res

  def hamiltonianPath(g: Graph): Option[Seq[Edge]] =
    val n: Int = g.vertexSet.size
    val nG: Graph = Graph(Matrix.fromBlock(g.adjMat, IntMatrix.ones(n, 1), IntMatrix.ones(1, n), IntMatrix.zeros(1, 1)))
    val p = hamiltonianCycle(nG).map(_.filter(p => p._1 < n && p._2 < n))
    p.map(some => if(some.size == n) some.tail else some)

  def dominatingSet(g: Graph)(k: Int): Option[Set[Vertex]] =
    val str: Seq[String] = Range(0, g.vertexSet.size).map(_.toString)
    val vars: Seq[Z3Type] = intConst(str)
    val cst1: Z3Type = andAll((for (v1 <- 0 until g.vertexSet.size) yield sum(intConst((g.adjList(v1) + v1).map(_.toString).toList)) >= 1).toList)
    val cst2: Z3Type = vars >= 0 && vars <= 1 && sum(vars) === k

    val (sol, z) = solve(cst1 && cst2, str)
    val res = filterSol(sol).map(_.toSet)
    z.delete()
    res

  def domaticPartition(g: Graph)(k: Int): Option[Seq[Set[Vertex]]] = 
    val str: Seq[String] = for(i <- 0 until g.vertexSet.size; j <- 0 until k) yield s"${i},${j}"
    val vars: Seq[Z3Type] = intConst(str)
    val cst1: Z3Type = andAll((for(i <- 0 until k) yield andAll(for (v1 <- 0 until g.vertexSet.size) yield sum(intConst((g.adjList(v1) + v1).map(v => s"${v},${i}").toList)) >= 1)))
    val cst2: Z3Type = andAll(for(v1 <- 0 until g.vertexSet.size) yield sum(for (i <- 0 until k) yield intConst(s"${v1},${i}")) === 1)
    val cst3: Z3Type = andAll(for(i <- 0 until k) yield sum(for (v1 <- 0 until g.vertexSet.size) yield intConst(s"${v1},${i}")) >= 1)
    val cst4: Z3Type = vars >= 0
    val (sol, z) = solve(cst1 && cst2 && cst3 && cst4, str)
    val res = toInt(sol).map(_.zipWithIndex.foldLeft(ArraySeq.fill(k)(Set(): Set[Vertex]))((acc, p) => 
      if (p._1 >= 1) acc.updated(p._2 % k, acc(p._2 % k) + (p._2 / k)) else acc))
    z.delete()
    res

  def indset(g: Graph)(k: Int) : Option[Set[Int]] = 
  if (g.edgeSet.size > 0)
    val str: Seq[String] = Range(0, g.vertexSet.size).map(_.toString)
    val vars: Seq[Z3Type] = intConst(str)
    val cst1: Z3Type = andAll((for (v1, v2) <- g.edgeSet yield intConst(v1.toString) + intConst(v2.toString) <= 1).toList)
    val cst2: Z3Type = vars >= 0 && sum(vars) >= k

    val (sol, z) = solve(cst1 && cst2, str)
    val res = filterSol(sol).map(_.toSet)
    z.delete()
    res
  else if (g.vertexSet.size >= k) Some(Range(0, k).toSet) 
  else None


  def kRegularInducedSubgraph(g: Graph)(k: Int)(v: Int) : Option[Set[Int]] = 
    if (g.edgeSet.size > 0)
      val str: Seq[String] = Range(0, g.vertexSet.size).map(_.toString)
      val vars: Seq[Z3Type] = intConst(str)
      val cst1: Z3Type = andAll((for (v1 <- 0 until g.vertexSet.size) yield sum(intConst(g.adjList(v1).map(_.toString).toList)) === k).toList)
      val cst2: Z3Type = vars >= 0 && vars <= 1
      val cst3: Z3Type = sum(vars) === v

      val (sol, z) = solve(cst1 && cst2 && cst3, str)
      val res = filterSol(sol).map(_.toSet)
      z.delete()
      res
    else if (g.vertexSet.size >= k) Some(Range(0, k).toSet) 
    else None



  def maxDomaticPartition(g: Graph): Seq[Set[Vertex]] =
    max(g.vertexSet.map(Set(_)).toList, 2, domaticPartition(g), g.vertexSet.size)
  def maxIndset(g: Graph): Set[Int] =
    max(Set(0), 2, indset(g), g.vertexSet.size)
  def maxClique(g: Graph): Set[Int] =
    max(Set(0), 2, clique(g), g.vertexSet.size)
  def minColoring(g: Graph): Seq[Int] =
    min(Range(0, g.vertexSet.size), g.vertexSet.size - 1, coloring(g), 1)
  def minDominatingSet(g: Graph): Set[Int] =
    min(g.vertexSet, g.vertexSet.size - 1, dominatingSet(g), 1)
  def minVertexCover(g: Graph): Set[Int] =
    min(g.vertexSet, g.vertexSet.size - 1, vertexCover(g), 1)

}