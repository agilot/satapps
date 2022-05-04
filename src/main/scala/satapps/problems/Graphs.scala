package satapps.problems

import satapps.*
import Z3.{*, given}
import BooleanMatricesOps.{*, given}
import scala.collection.immutable.ArraySeq
import Extensions.*
import z3.scala.*

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

  object Indset extends MaxProblem[Graph, Set[Int]] {
    override protected def constraints(g: Graph, k: Int) =
      require(k >= 0)
      val str: Seq[String] = Range(0, g.vertexSet.size).map(_.toString)
      val vars: Seq[Z3Type] = intConst(str)
      val cst1: Z3Type = andAll((for (v1, v2) <- g.edgeSet yield intConst(v1.toString) + intConst(v2.toString) <= 1).toList)
      val cst2: Z3Type = vars >= 0 && sum(vars) >= k
      (cst1 && cst2, str)
    override protected def convert(g: Graph, k: Int, sol: Seq[Z3AST]) = filterSol(sol).toSet
    override def max(g: Graph): Set[Int] = max(g, Set(0), 1, g.vertexSet.size)
  }

  object VertexCover extends MinProblem[Graph, Set[Int]] {
    override protected def constraints(g: Graph, k: Int) =
      val str: Seq[String] = Range(0, g.vertexSet.size).map(_.toString)
      val vars: Seq[Z3Type] = intConst(str)
      val cst1: Z3Type = andAll((for (v1, v2) <- g.edgeSet yield intConst(v1.toString) + intConst(v2.toString) >= 1).toList)
      val cst2: Z3Type = vars >= 0 && sum(vars) <= k
      (cst1 && cst2, str)
    override protected def convert(g: Graph, k: Int, sol: Seq[Z3AST]) = filterSol(sol).toSet
    override def min(g: Graph): Set[Int] = min(g, g.vertexSet, g.vertexSet.size, 1)
  }

  object Coloring extends MinProblem[Graph, Map[Vertex, Int]] {
    override protected def constraints(g: Graph, c: Int) =
      val str: Seq[String] = 
        for(i <- 0 until g.vertexSet.size; j <- 0 until c)
          yield s"${i},${j}"
      val vars: Seq[Z3Type] = intConst(str)
      val cst1: Z3Type = vars >= 0
      val cst2: Z3Type = andAll((for((v1, v2) <- g.edgeSet; i <- 0 until c) yield
        intConst(s"${v1},${i}") + intConst(s"${v2},${i}") <= 1).toList)
      val cst3: Z3Type = andAll((for(v <- 0 until g.vertexSet.size) yield sum(for(i <- 0 until c) yield intConst(s"${v},${i}")) === 1))
      (cst1 && cst2 && cst3, str)
    override protected def convert(g: Graph, c: Int, sol: Seq[Z3AST]) = 
      toInt(sol).zipWithIndex.filter((cs, idx) => cs >= 1).map((cs, idx) => idx % c).zipWithIndex.map(p => (p._2, p._1)).toMap

    override def min(g: Graph): Map[Vertex, Int] = min(g, Range(0, g.vertexSet.size).zipWithIndex.toMap, g.vertexSet.size, 1)
  }

  object Clique extends BasicMaxProblem[Graph, Set[Int]]{
    override def search(g: Graph, k: Int) = Indset.search(g.nonReflComplement, k)
    override def decision(g: Graph, k: Int) = Indset.decision(g.nonReflComplement, k)
    override def max(g: Graph) = Indset.max(g.nonReflComplement)
  }

  object CliqueCover extends BasicMinProblem[Graph, Seq[Set[Int]]]{
    override def search(g: Graph, k: Int) = 
      Coloring.search(g.nonReflComplement, k).map(_.foldLeft(ArraySeq.fill(k)(Set(): Set[Vertex]))((acc, p) => acc.updated(p._2, acc(p._2) + p._1)))
    override def decision(g: Graph, k: Int) = Coloring.decision(g.nonReflComplement, k)
    override def min(g: Graph) = min(g, Range(0, g.vertexSet.size).map(Set(_)), g.vertexSet.size, 1)
  }

  object EdgeColoring extends MinProblem[Graph, Map[Edge, Int]] {
    override protected def constraints(g: Graph, c: Int) =
      val str: Seq[String] = 
        for(e <- g.edgeOrderedList; j <- 0 until c)
          yield s"${e},${j},"
      val vars: Seq[Z3Type] = intConst(str)
      val cst1: Z3Type = vars >= 0
      val cst2: Z3Type = andAll((for(v <- g.vertexSet; i <- 0 until c) yield
        sum(g.incidence(v).map(e => intConst(s"${e},${i}")).toList) <= 1).toList)
      val cst3: Z3Type = andAll((for(e <- g.edgeSet) yield sum(for(i <- 0 until c) yield intConst(s"${e},${i}")) === 1).toList)
      (cst1 && cst2 && cst3, str)
    override protected def convert(g: Graph, c: Int, sol: Seq[Z3AST]) = 
      g.edgeOrderedList.zip(toInt(sol).zipWithIndex.filter((cs, idx) => cs >= 1).map((cs, idx) => idx % c)).toMap
    override def min(g: Graph): Map[Edge, Int] = min(g, g.edgeSet.toList.zipWithIndex.toMap, g.edgeSet.size, 1)
  }  

  object DominatingSet extends MinProblem[Graph, Set[Int]] {
    override protected def constraints(g: Graph, k: Int) =
      val str: Seq[String] = Range(0, g.vertexSet.size).map(_.toString)
      val vars: Seq[Z3Type] = intConst(str)
      val cst1: Z3Type = andAll((for (v1 <- 0 until g.vertexSet.size) yield sum(intConst((g.adjList(v1) + v1).map(_.toString).toList)) >= 1).toList)
      val cst2: Z3Type = vars >= 0 && vars <= 1 && sum(vars) === k
      (cst1 && cst2, str)
    override protected def convert(g: Graph, k: Int, sol: Seq[Z3AST]) = filterSol(sol).toSet
    override def min(g: Graph): Set[Int] = min(g, g.vertexSet, g.vertexSet.size, 1)
  }

  object DomaticPartition extends MaxProblem[Graph, Seq[Set[Vertex]]]{
    override protected def constraints(g: Graph, k: Int) =
      val str: Seq[String] = for(i <- 0 until g.vertexSet.size; j <- 0 until k) yield s"${i},${j}"
      val vars: Seq[Z3Type] = intConst(str)
      val cst1: Z3Type = andAll((for(i <- 0 until k) yield andAll(for (v1 <- 0 until g.vertexSet.size) yield sum(intConst((g.adjList(v1) + v1).map(v => s"${v},${i}").toList)) >= 1)))
      val cst2: Z3Type = andAll(for(v1 <- 0 until g.vertexSet.size) yield sum(for (i <- 0 until k) yield intConst(s"${v1},${i}")) === 1)
      val cst3: Z3Type = andAll(for(i <- 0 until k) yield sum(for (v1 <- 0 until g.vertexSet.size) yield intConst(s"${v1},${i}")) >= 1)
      val cst4: Z3Type = vars >= 0
      (cst1 && cst2 && cst3 && cst4, str)
    override protected def convert(g: Graph, k: Int, sol: Seq[Z3AST]) = 
      toInt(sol).zipWithIndex.foldLeft(ArraySeq.fill(k)(Set(): Set[Vertex]))((acc, p) => 
      if (p._1 >= 1) acc.updated(p._2 % k, acc(p._2 % k) + (p._2 / k)) else acc)
    override def max(g: Graph): Seq[Set[Vertex]] = max(g, g.vertexSet.map(Set(_)).toList, 1, g.vertexSet.size)
  }

  object TotalDominatingSet extends MinProblem[Graph, Set[Vertex]]{
    override protected def constraints(g: Graph, k: Int) =
      val str: Seq[String] = Range(0, g.vertexSet.size).map(_.toString)
      val vars: Seq[Z3Type] = intConst(str)
      val cst1: Z3Type = andAll((for (v1 <- 0 until g.vertexSet.size) yield sum(intConst((g.adjList(v1)).map(_.toString).toList)) >= 1).toList)
      val cst2: Z3Type = vars >= 0 && vars <= 1 && sum(vars) === k
      (cst1 && cst2, str)
    override protected def convert(g: Graph, k: Int, sol: Seq[Z3AST]) = filterSol(sol).toSet
    override def min(g: Graph) = 
      if(g.adjList.exists((v, s) => s.isEmpty))
        throw IllegalArgumentException("The graph has an isolated vertex")
      else
        min(g, g.vertexSet, g.vertexSet.size, 1)
  }

  object ConnectedDominatingSet extends MinProblem[Graph, Set[Vertex]]{
    override protected def constraints(g: Graph, k: Int) =
      val n: Int = g.vertexSet.size
      val esl: Seq[Edge] = g.undirected(false).edgeSet.toSeq
      val strX: Seq[String] = Range(0, n).map(_.toString)
      val strY: Seq[String] = esl.map(_.toString)
      val strZ: Seq[String] = esl.flatMap(e => Range(0, g.vertexSet.size).map(v => s"${e},${v}"))
      val str = strX ++ strY ++ strZ
      val varsX: Seq[Z3Type] = intConst(strX)
      val varsY: Seq[Z3Type] = intConst(strY)
      val vars: Seq[Z3Type] = intConst(str)

      val cst1: Z3Type = andAll((for (v1 <- 0 until g.vertexSet.size) yield sum(intConst((g.adjList(v1) + v1).map(_.toString).toList)) >= 1).toList)
      val cst2: Z3Type = vars >= 0 && vars <= 1 && sum(varsX) === k
      val cst3a: Z3Type = sum(varsY) === (sum(varsX) - 1)
      val cst3b: Z3Type = andAll(for(e <- esl) yield (intConst(e.toString) <= intConst(e._1.toString)) && (intConst(e.toString) <= intConst(e._2.toString)))
      val cst3c: Z3Type = andAll(for(e <- esl; v <- 0 until n) yield intConst(s"${e},${v}") <= intConst(e.toString) && intConst(s"${e},${v}") <= intConst(v.toString))
      val cst3d: Z3Type = andAll(for((i, j) <- esl; v <- 0 until n) yield intConst(s"${(j, i)},${v}") <= intConst((i, j).toString) && intConst(s"${(j, i)},${v}") <= intConst(v.toString))
      val cst3e: Z3Type = andAll(for(e <- esl; v <- 0 until n) yield 
        ((intConst(e.toString) - 3 + intConst(e._1.toString) + intConst(e._2.toString) + intConst(v.toString)) <= (intConst(s"${e},${v}") + intConst(s"${(e._2, e._1)},${v}"))) &&
        ((intConst(s"${e},${v}") + intConst(s"${(e._2, e._1)},${v}")) <= (intConst(e.toString) + 3 - intConst(e._1.toString) - intConst(e._2.toString) - intConst(v.toString))))
      val cst3f: Z3Type = andAll(for(e <- esl) yield 
        ((intConst(e._1.toString) + intConst(e._2.toString) - 1) <= (sum(for(k0 <- 0 until n; if k0 != e._1 && k0 != e._2) yield intConst(s"${(e._1, k0)}${e._2}")) + intConst(e.toString))) &&
        ((sum(for(k0 <- 0 until n; if k0 != e._1 && k0 != e._2) yield intConst(s"${(e._1, k0)}${e._2}")) + intConst(e.toString)) <= (3 - intConst(e._1.toString) + intConst(e._2.toString))))
      (cst1 && cst2 && cst3a && cst3b && cst3c && cst3d && cst3e && cst3f, str)
    override protected def convert(g: Graph, k: Int, sol: Seq[Z3AST]) = filterSol(sol.take(g.vertexSet.size)).toSet
    override def min(g: Graph) = 
      if (g.connected)
        min(g, g.vertexSet, g.vertexSet.size, 1)
      else throw IllegalArgumentException("The graph is not connected")
  }

  object IndependentDominatingSet extends MinProblem[Graph, Set[Int]] {
    override protected def constraints(g: Graph, k: Int) =
      val str: Seq[String] = Range(0, g.vertexSet.size).map(_.toString)
      val vars: Seq[Z3Type] = intConst(str)
      val cst1: Z3Type = andAll((for (v1 <- 0 until g.vertexSet.size) yield sum(intConst((g.adjList(v1) + v1).map(_.toString).toList)) >= 1).toList)
      val cst2: Z3Type = vars >= 0 && sum(vars) === k
      val cst3: Z3Type = andAll((for (v1, v2) <- g.edgeSet yield intConst(v1.toString) + intConst(v2.toString) <= 1).toList)
      (cst1 && cst2 && cst3, str)
    override protected def convert(g: Graph, k: Int, sol: Seq[Z3AST]) = filterSol(sol).toSet
    override def min(g: Graph): Set[Int] = min(g, g.vertexSet, g.vertexSet.size, 1)
  }

  object AsymetricTravelingSalesperson extends BiProblem[Graph, Int, Seq[Edge]]{
    override protected def constraints(g: Graph, d: Int) =
      if(g.vertexSet.size > 2 && g.connected)
        (tspConstraints(g)(d), g.edgeOrderedList.map((v1, v2) => s"${v1},${v2}"))
      else (false, Nil)
    override protected def convert(g: Graph, d: Int, sol: Seq[Z3AST]) =
      toInt(sol).zip(g.edgeOrderedList).filter((v, e) => v > 0).map((v, e) => e)
  }

  object SymetricTravelingSalesperson extends BasicBiProblem[Graph, Int, Seq[Edge]]{
    override def search(g: Graph, d: Int) = AsymetricTravelingSalesperson.search(g.undirected(true), d)
    override def decision(g: Graph, d: Int) = AsymetricTravelingSalesperson.decision(g.undirected(true), d)
  }

  object DirectedHamiltonianCycle extends BasicProblem[Graph, Seq[Edge]]{
    override def search(g: Graph) = AsymetricTravelingSalesperson.search(g.unweighted, g.vertexSet.size)
    override def decision(g: Graph) = AsymetricTravelingSalesperson.decision(g.unweighted, g.vertexSet.size)
  }
  
  object UndirectedHamiltonianCycle extends BasicProblem[Graph, Seq[Edge]]{
    override def search(g: Graph) = DirectedHamiltonianCycle.search(g.undirected(true))
    override def decision(g: Graph) = DirectedHamiltonianCycle.decision(g.undirected(true))
  }
  
  object DirectedHamiltonianPath extends BasicProblem[Graph, Seq[Edge]]{
    override def search(g: Graph) = 
      val n: Int = g.vertexSet.size
      val nG: Graph = Graph(Matrix.fromBlock(g.adjMat, IntMatrix.ones(n, 1), IntMatrix.ones(1, n), IntMatrix.zeros(1, 1)))
      val p = DirectedHamiltonianCycle.search(nG).map(_.filter(p => p._1 < n && p._2 < n))
      p.map(some => if(some.size == n) some.tail else some)
    override def decision(g: Graph) = search(g).isDefined
  }
  
  object UndirectedHamiltonianPath extends BasicProblem[Graph, Seq[Edge]]{    
    override def search(g: Graph) = DirectedHamiltonianPath.search(g.undirected(true))
    override def decision(g: Graph) = DirectedHamiltonianPath.decision(g.undirected(true))
  }

  object DirectedHamiltonianFixedPath extends TriProblem[Graph, Vertex, Vertex, Seq[Edge]]{
    override protected def constraints(g: Graph, start: Vertex, end: Vertex) =
      if(g.connected)
        val n: Int = g.vertexSet.size
        val nG: Graph = Graph(Matrix.fromBlock(g.adjMat, IntMatrix.ones(n, 1), IntMatrix.ones(1, n), IntMatrix.zeros(1, 1)))
        val str: Seq[String] = nG.edgeOrderedList.map((v1, v2) => s"${v1},${v2}")
        val cstStart: Z3Type = intConst(s"${n},${start}") === 1
        val cstEnd: Z3Type = intConst(s"${end},${n}") === 1
        (tspConstraints(nG)(n + 1) && cstStart && cstEnd, str)
      else (false, Nil)
    override protected def convert(g: Graph, start: Vertex, end: Vertex, sol: Seq[Z3AST]) =
      val n: Int = g.vertexSet.size
      val nG: Graph = Graph(Matrix.fromBlock(g.adjMat, IntMatrix.ones(n, 1), IntMatrix.ones(1, n), IntMatrix.zeros(1, 1)))
      toInt(sol).zip(nG.edgeOrderedList).filter((v, e) => v > 0).map((v, e) => e)
  }
  object UndirectedHamiltonianFixedPath extends BasicTriProblem[Graph, Vertex, Vertex, Seq[Edge]]{    
    override def search(g: Graph, start: Vertex, end: Vertex) = DirectedHamiltonianFixedPath.search(g.undirected(true), start, end)
    override def decision(g: Graph, start: Vertex, end: Vertex) = DirectedHamiltonianFixedPath.decision(g.undirected(true), start, end)
  }
  
/***********************Constraints***********************/
  private def tspConstraints(g: Graph)(d: Int): Z3Type = 
      val esl: Seq[Edge] = g.edgeOrderedList
      val str: Seq[String] = esl.map((v1, v2) => s"${v1},${v2}")
      val vars: Seq[Z3Type] = intConst(str)
      val cst1: Z3Type = andAll(g.adjList.map((v1, se) => sum(se.map(v2 => intConst(s"${v1},${v2}")).toList) === 1).toList)
      val cst2: Z3Type = andAll(g.inNeighb.map((v2, se) => sum(se.map(v1 => intConst(s"${v1},${v2}")).toList) === 1).toList)
      val cst3: Z3Type = vars >= 0 && vars <= 1
      val cst4: Z3Type = sum(esl.map(e => intConst(s"${e._1}, ${e._2}") * g.wMap(e))) <= d
      return cst1 && cst2 && cst3 && cst4
}