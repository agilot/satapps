package satapps.problems

import satapps.*
import Z3.{*, given}
import BooleanMatricesOps.{*, given}
import scala.collection.immutable.ArraySeq
import Extensions.*

object Graphs {




  // def kRegularInducedSubgraph(g: Graph)(k: Int)(v: Int) : Option[Set[Int]] = 
  //   if (g.edgeSet.size > 0)
  //     val str: Seq[String] = Range(0, g.vertexSet.size).map(_.toString)
  //     val vars: Seq[Z3Type] = intConst(str)
  //     val cst1: Z3Type = andAll((for (v1 <- 0 until g.vertexSet.size) yield sum(intConst(g.adjList(v1).map(_.toString).toList)) === k).toList)
  //     val cst2: Z3Type = vars >= 0 && vars <= 1
  //     val cst3: Z3Type = sum(vars) === v

  //     val (sol, z) = solve(cst1 && cst2 && cst3, str)
  //     val res = filterSol(sol).map(_.toSet)
  //     z.delete()
  //     res
  //   else if (g.vertexSet.size >= k) Some(Range(0, k).toSet) 
  //   else None

/***********************Independent set***********************/

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
  
  def indsetDecision(g: Graph)(k: Int) : Boolean = indset(g)(k).isDefined

  def maxIndset(g: Graph): Set[Int] =
    max(Set(0), 2, indset(g), g.vertexSet.size)

  def independenceNumber(g: Graph): Int = maxIndset(g).size

/***********************Vertex Cover***********************/
  def vertexCover(g: Graph)(k: Int): Option[Set[Vertex]] =
    val str: Seq[String] = Range(0, g.vertexSet.size).map(_.toString)
    val vars: Seq[Z3Type] = intConst(str)
    val cst1: Z3Type = andAll((for (v1, v2) <- g.edgeSet yield intConst(v1.toString) + intConst(v2.toString) >= 1).toList)
    val cst2: Z3Type = vars >= 0 && sum(vars) <= k

    val (sol, z) = solve(cst1 && cst2, str)
    val res = filterSol(sol).map(_.toSet)
    z.delete()
    res
  
  def vertexCoverDecision(g: Graph)(k: Int): Boolean = vertexCover(g)(k).isDefined

  def minVertexCover(g: Graph): Set[Int] =
    min(g.vertexSet, g.vertexSet.size - 1, vertexCover(g), 1)

  def vertexCoverNumber(g: Graph): Int = minVertexCover(g).size

/***********************Clique***********************/
  def clique(g: Graph)(k: Int): Option[Set[Int]] =
    require(k >= 0)
    indset(g.nonReflComplement)(k)

  def cliqueDecision(g: Graph)(k: Int): Boolean = clique(g)(k).isDefined

  def maxClique(g: Graph): Set[Int] =
    max(Set(0), 2, clique(g), g.vertexSet.size)

  def cliqueNumber(g: Graph): Int = maxClique(g).size

  def cliqueCover(g: Graph)(k: Int): Option[Seq[Set[Int]]] =
    coloring(g.nonReflComplement)(k).map(_.zipWithIndex.foldLeft(ArraySeq.fill(k)(Set(): Set[Vertex]))((acc, p) => acc.updated(p._1, acc(p._1) + p._2)))

  def cliqueCoverDecision(g: Graph)(k: Int): Boolean = cliqueCover(g)(k).isDefined
  
  def minCliqueCover(g: Graph): Seq[Set[Int]] =
    min(Range(0, g.vertexSet.size).map(Set(_)), g.vertexSet.size - 1, cliqueCover(g), 1)

  def cliqueCoverNumber(g: Graph): Int = minCliqueCover(g).size

/***********************Coloring***********************/

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
  
  def coloringDecision(g: Graph)(c: Int): Boolean = coloring(g)(c).isDefined

  def minColoring(g: Graph): Seq[Int] =
    min(Range(0, g.vertexSet.size), g.vertexSet.size - 1, coloring(g), 1)
  
  def chromaticNumber(g: Graph): Int = minColoring(g).toSet.size

  def edgeColoring(g: Graph)(c: Int): Option[Map[Edge, Int]] =
    val eSeq: Seq[Edge] = g.edgeSet.toSeq
    val str: Seq[String] = 
      for(e <- eSeq; j <- 0 until c)
        yield s"${e},${j},"
    val vars: Seq[Z3Type] = intConst(str)
    val cst1: Z3Type = vars >= 0
    val cst2: Z3Type = andAll((for(v <- g.vertexSet; i <- 0 until c) yield
      sum(g.incidence(v).map(e => intConst(s"${e},${i}")).toList) <= 1).toList)
    val cst3: Z3Type = andAll((for(e <- g.edgeSet) yield sum(for(i <- 0 until c) yield intConst(s"${e},${i}")) === 1).toList)

    val (sol, z) = solve(cst1 && cst2 && cst3, str)
    val res = toInt(sol).map(_.zipWithIndex.filter((cs, idx) => cs >= 1).map((cs, idx) => idx % c)) match{
      case None => None
      case Some(s) => Some(eSeq.zip(s).toMap)
    }
    z.delete()
    res

  def edgeColoringDecision(g: Graph)(c: Int): Boolean = edgeColoring(g)(c).isDefined

  def minEdgeColoring(g: Graph): Map[Edge, Int] = min(g.edgeSet.toList.zipWithIndex.toMap, g.edgeSet.size - 1, edgeColoring(g), 1)
  
  def edgeChromaticNumber(g: Graph): Int = minEdgeColoring(g).values.size

/***********************Dominating set***********************/

  def dominatingSet(g: Graph)(k: Int): Option[Set[Vertex]] =
    val str: Seq[String] = Range(0, g.vertexSet.size).map(_.toString)
    val vars: Seq[Z3Type] = intConst(str)
    val cst1: Z3Type = andAll((for (v1 <- 0 until g.vertexSet.size) yield sum(intConst((g.adjList(v1) + v1).map(_.toString).toList)) >= 1).toList)
    val cst2: Z3Type = vars >= 0 && vars <= 1 && sum(vars) === k

    val (sol, z) = solve(cst1 && cst2, str)
    val res = filterSol(sol).map(_.toSet)
    z.delete()
    res

  def minDominatingSet(g: Graph): Set[Int] =
    min(g.vertexSet, g.vertexSet.size - 1, dominatingSet(g), 1)

  def dominationNumber(g: Graph): Int = minDominatingSet(g).size
  
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

  def maxDomaticPartition(g: Graph): Seq[Set[Vertex]] =
    max(g.vertexSet.map(Set(_)).toList, 2, domaticPartition(g), g.vertexSet.size)

  def domaticNumber(g: Graph): Int = maxDomaticPartition(g).size

  def totalDominatingSet(g: Graph)(k: Int): Option[Set[Vertex]] =
    if(k > 1)
      val str: Seq[String] = Range(0, g.vertexSet.size).map(_.toString)
      val vars: Seq[Z3Type] = intConst(str)
      val cst1: Z3Type = andAll((for (v1 <- 0 until g.vertexSet.size) yield sum(intConst((g.adjList(v1)).map(_.toString).toList)) >= 1).toList)
      val cst2: Z3Type = vars >= 0 && vars <= 1 && sum(vars) === k
      val (sol, z) = solve(cst1 && cst2, str)
      val res = filterSol(sol).map(_.toSet)
      z.delete()
      res
    else 
      val set: Set[Vertex] = g.vertexSet.map(v => if(g.adjList(v).size + g.inNeighb(v).size == g.vertexSet.size - 1) Set(v) else Set()).reduce(_ ++ _) 
      if (set.isEmpty) None else Some(set)
  
  def totalDominatingSetDecision(g: Graph)(k: Int): Boolean = totalDominatingSet(g)(k).isDefined

  def minTotalDominatingSet(g: Graph): Option[Set[Vertex]] =
    if (g.connected)
      Some(min(g.vertexSet, g.vertexSet.size - 1, totalDominatingSet(g), 1))
    else None
  
  def totalDominationNumber(g: Graph): Option[Int] =
    minTotalDominatingSet(g).map(_.size)

/***********************Independent dominating set***********************/

  def independentDominatingSet(g: Graph)(k: Int): Option[Set[Vertex]] =
    val str: Seq[String] = Range(0, g.vertexSet.size).map(_.toString)
    val vars: Seq[Z3Type] = intConst(str)
    val cst1: Z3Type = andAll((for (v1 <- 0 until g.vertexSet.size) yield sum(intConst((g.adjList(v1) + v1).map(_.toString).toList)) >= 1).toList)
    val cst2: Z3Type = vars >= 0 && sum(vars) === k
    val cst3: Z3Type = andAll((for (v1, v2) <- g.edgeSet yield intConst(v1.toString) + intConst(v2.toString) <= 1).toList)

    val (sol, z) = solve(cst1 && cst2 && cst3, str)
    val res = filterSol(sol).map(_.toSet)
    z.delete()
    res

  def minIndependentDominatingSet(g: Graph): Set[Int] =
    min(g.vertexSet, g.vertexSet.size - 1, independentDominatingSet(g), 1)

  def independentDominationNumber(g: Graph): Int = minIndependentDominatingSet(g).size
  
/***********************Hamiltonian***********************/

  def hamiltonianCycle(g: Graph): Option[Seq[Edge]] =
    travelingSalesman(g.undirected)(g.vertexSet.size)

  def hamiltonianCycleDecision(g: Graph): Boolean = hamiltonianCycle(g).isDefined

  def hamiltonianPath(g: Graph): Option[Seq[Edge]] =
    val n: Int = g.vertexSet.size
    val nG: Graph = Graph(Matrix.fromBlock(g.adjMat, IntMatrix.ones(n, 1), IntMatrix.ones(1, n), IntMatrix.zeros(1, 1)))
    val p = hamiltonianCycle(nG).map(_.filter(p => p._1 < n && p._2 < n))
    p.map(some => if(some.size == n) some.tail else some)

  def hamiltonianPathDecision(g: Graph): Boolean = hamiltonianPath(g).isDefined

  def travelingSalesman(g: Graph)(d: Int): Option[Seq[Edge]] =
    if(g.vertexSet.size > 2 && g.connected)
      val esl: Seq[Edge] = g.edgeSet.toList
      val str: Seq[String] = esl.map((v1, v2) => s"${v1},${v2}")
      val vars: Seq[Z3Type] = intConst(str)
      val cst1: Z3Type = andAll(g.adjList.map((v1, se) => sum(se.map(v2 => intConst(s"${v1},${v2}")).toList) === 1).toList)
      val cst2: Z3Type = andAll(g.inNeighb.map((v2, se) => sum(se.map(v1 => intConst(s"${v1},${v2}")).toList) === 1).toList)
      val cst3: Z3Type = vars >= 0 && vars <= 1
      val cst4: Z3Type = sum(esl.map(e => intConst(s"${e._1}, ${e._2}") * g.wMap(e))) <= d

      val (sol, z) = solve(cst1 && cst2 && cst3 && cst4, str)
      val res = toInt(sol).map(some => some.zip(esl).filter((v, e) => v > 0).map((v, e) => e))
      z.delete()
      res
    else None

  def travelingSalesmanDecision(g: Graph)(d: Int): Boolean = travelingSalesman(g)(d).isDefined

/***********************Induced subgraphs***********************/


}