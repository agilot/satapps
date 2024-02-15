// package satapps.problems

// import satapps.*
// import ConstrProg.{*, given}
// import BooleanMatricesOps.{*, given}
// import scala.collection.immutable.ArraySeq
// import Extensions.*
// import Iter.*
// import z3.scala.*

// object Graphs {

//   private def isDominating(g: Graph, set: Set[Vertex]): Boolean = g.neighb(set) ++ set == g.vertexSet


//   // def kRegularInducedSubgraph(g: Graph)(k: Int)(v: Int) : Option[Set[Int]] = 
//   //   if (g.edgeSet.size > 0)
//   //     val str: Seq[String] = Range(0, g.vertexSet.size).map(_)
//   //     val vars: Seq[BoolConstr] = IntVar(str)
//   //     val cst1: BoolConstr = And((for (v1 <- 0 until g.vertexSet.size) yield Add(IntVar(g.adjList(v1).map(_).toList)) === k).toList)
//   //     val cst2: BoolConstr = vars >= 0 && vars <= 1
//   //     val cst3: BoolConstr = Add(vars) === v

//   //     val (sol, z) = solve(cst1 && cst2 && cst3, str)
//   //     val res = filterSol(sol).map(_.toSet)
//   //     z.delete()
//   //     res
//   //   else if (g.vertexSet.size >= k) Some(Range(0, k).toSet) 
//   //   else None

//   object Indset extends MaxProblem[Graph, Set[Vertex]] {
//     override protected def constraints(g: Graph, k: Int) =
//       require(k >= 0)
//       val vars: Seq[IntConstr] = IntVar(g.vertexSet.toList)
//       And((for (v1, v2) <- g.edgeSet yield IntVar(v1) + IntVar(v2) <= 1).toList) && vars >= 0 && vars <= 1 && Add(vars) === k
//     override protected def convert(g: Graph, k: Int, sol: NumQuery) = sol.toInt.filterIdx
    
//     override def verify(g: Graph, k: Int, sol: Set[Vertex]) = sol.size == k && g.induced(sol).isIndependent
//     override def max(g: Graph): Option[Set[Vertex]] = max(g, 1, g.vertexSet.size)
//   }

//   object VertexCover extends MinProblem[Graph, Set[Int]] {
//     override protected def constraints(g: Graph, k: Int) =
//       val vars: Seq[IntConstr] = IntVar(g.vertexSet.toList)
//       And((for (v1, v2) <- g.edgeSet yield IntVar(v1) + IntVar(v2) >= 1).toList) && vars >= 0 && Add(vars) === k
//     override protected def convert(g: Graph, k: Int, sol: NumQuery) = sol.toInt.filterIdx
//     override def verify(g: Graph, k: Int, sol: Set[Int]) = g.edgeSet.forall(sol(_) || sol(_)) && sol.size == k
//     override def min(g: Graph): Option[Set[Int]] = min(g, g.vertexSet.size, 1)
//   }

//   object Coloring extends MinProblem[Graph, Map[Vertex, Int]] {
//     override protected def constraints(g: Graph, c: Int) =
//       val vars: Seq[IntConstr] = IntVar(cartesian(g.vertexSet, Range(0, c)).toList)
//       val cst1: BoolConstr = vars >= 0
//       val cst2: BoolConstr = And((for((v1, v2) <- g.edgeSet; i <- 0 until c) yield
//         IntVar((v1, i)) + IntVar((v2, i)) <= 1).toList)
//       val cst3: BoolConstr = And((for(v <- 0 until g.vertexSet.size) yield Add(for(i <- 0 until c) yield IntVar((v, i))) === 1))
//       cst1 && cst2 && cst3
//     override protected def convert(g: Graph, c: Int, sol: NumQuery) = 
//       sol.toInt.filterPositive.map((s, _) => s.split(",") match{case Array(str1, str2) => (str1.toInt, str2.toInt)}).toMap
//     override def min(g: Graph): Option[Map[Vertex, Int]] = min(g, g.vertexSet.size, 1)
//     override def verify(g: Graph, c: Int, sol: Map[Vertex, Int]): Boolean = 
//       g.edgeSet.forall(sol(_) != sol(_)) && sol.values.size == c
//   }

//   object Clique extends BasicMaxProblem[Graph, Set[Vertex]]{
//     override def search(g: Graph, k: Int) = Indset.search(g.nonReflComplement, k)
//     override def decide(g: Graph, k: Int) = Indset.decide(g.nonReflComplement, k)
//     override def enumerate(g: Graph, k: Int) = Indset.enumerate(g.nonReflComplement, k)
//     override def verify(g: Graph, k: Int, sol: Set[Vertex]) = sol.size == k && g.induced(sol).isClique
//     override def max(g: Graph) = Indset.max(g.nonReflComplement)
//   }

//   object CliqueCover extends BasicMinProblem[Graph, Seq[Set[Vertex]]]{
//     override def search(g: Graph, k: Int) = 
//       Coloring.search(g.nonReflComplement, k).map(_.foldLeft(ArraySeq.fill(k)(Set(): Set[Vertex]))((acc, p) => acc.updated(p._2, acc(p._2) + p._1)))
//     override def decide(g: Graph, k: Int) = Coloring.decide(g.nonReflComplement, k)
//     override def enumerate(g: Graph, k: Int) = 
//       Coloring.enumerate(g.nonReflComplement, k).map(_.foldLeft(ArraySeq.fill(k)(Set(): Set[Vertex]))((acc, p) => acc.updated(p._2, acc(p._2) + p._1)))
//     override def verify(g: Graph, k: Int, sol: Seq[Set[Vertex]]) = sol.isPartition(g.vertexSet) && sol.size == k
//     override def min(g: Graph) = min(g, g.vertexSet.size, 1)
//   }

//   object EdgeColoring extends MinProblem[Graph, Map[Edge, Int]] {
//     override protected def constraints(g: Graph, c: Int) =
//       val vars: Seq[IntConstr] = IntVar((for(e <- g.edgeSet; j <- 0 until c) yield s"${e},${j}").toSeq)
//       val cst1: BoolConstr = vars >= 0
//       val cst2: BoolConstr = And((for(v <- g.vertexSet; i <- 0 until c) yield
//         Add(g.incidence(v).map(e => IntVar(s"${e},${i}")).toList) <= 1).toList)
//       val cst3: BoolConstr = And((for(e <- g.edgeSet) yield Add(for(i <- 0 until c) yield IntVar(s"${e},${i}")) === 1).toList)
//       cst1 && cst2 && cst3
//     override protected def convert(g: Graph, c: Int, sol: NumQuery) = 
//       sol.toInt.filterPositive.map((k, _) => k match {case s"(${v1},${v2}),${c}" => ((v1.toInt, v2.toInt), c.toInt)}).toMap
//     override def verify(g: Graph, k: Int, sol: Map[Edge, Int]) = ???
//     override def min(g: Graph): Option[Map[Edge, Int]] = min(g, g.edgeSet.size, 1)
//   }  

//   object DominatingSet extends MinProblem[Graph, Set[Vertex]] {
//     override protected def constraints(g: Graph, k: Int) =
//       val vars: Seq[IntConstr] = IntVar(g.vertexSet.toList)
//       val cst1: BoolConstr = And((for (v1 <- 0 until g.vertexSet.size) yield Add(IntVar((g.adjList(v1) + v1).toList)) >= 1).toList)
//       val cst2: BoolConstr = vars >= 0 && vars <= 1 && Add(vars) === k
//       cst1 && cst2
//     override protected def convert(g: Graph, k: Int, sol: NumQuery) = sol.toInt.filterIdx
    
//     override def verify(g: Graph, k: Int, sol: Set[Vertex]) =
//       sol.size == k && isDominating(g, sol)
//     override def min(g: Graph): Option[Set[Vertex]] = min(g, g.vertexSet.size, 1)
//   }

//   object DomaticPartition extends MaxProblem[Graph, Seq[Set[Vertex]]]{
//     override protected def constraints(g: Graph, k: Int) =
//       val vars: Seq[IntConstr] = IntVar(cartesian(g.vertexSet, Range(0, k)).toSeq)
//       val cst1: BoolConstr = And((for(i <- 0 until k) yield And(for (v1 <- 0 until g.vertexSet.size) yield Add(IntVar((g.adjList(v1) + v1).map(v => (v, i)).toList)) >= 1)))
//       val cst2: BoolConstr = And((for(v1 <- g.vertexSet) yield Add(for (i <- 0 until k) yield IntVar((v1, i))) === 1).toSeq)
//       val cst3: BoolConstr = And(for(i <- 0 until k) yield Add(for (v1 <- 0 until g.vertexSet.size) yield IntVar((v1, i))) >= 1)
//       val cst4: BoolConstr = vars >= 0
//       cst1 && cst2 && cst3 && cst4
//     override protected def convert(g: Graph, k: Int, sol: NumQuery) = 
//       sol.toInt.filterPairIdx.foldLeft(ArraySeq.fill(k)(Set(): Set[Vertex]))((acc, p) => acc.updated(p._2, acc(p._2) + p._1))
//     override def verify(g: Graph, k: Int, sol: Seq[Set[Vertex]]) = ???
//     override def max(g: Graph): Option[Seq[Set[Vertex]]] = max(g, 1, g.vertexSet.size)
    
//   }

//   object TotalDominatingSet extends MinProblem[Graph, Set[Vertex]]{
//     override protected def constraints(g: Graph, k: Int) =
//       val vars: Seq[IntConstr] = IntVar(g.vertexSet.toSeq)
//       val cst1: BoolConstr = And((for (v1 <- g.vertexSet) yield Add(IntVar((g.adjList(v1)).toList)) >= 1).toList)
//       val cst2: BoolConstr = vars >= 0 && vars <= 1 && Add(vars) === k
//       cst1 && cst2
//     override protected def convert(g: Graph, k: Int, sol: NumQuery) = sol.toInt.filterIdx
//     override def verify(g: Graph, k: Int, sol: Set[Vertex]) = ???
//     override def min(g: Graph) = min(g, g.vertexSet.size, 1)
//   }

//   object ConnectedDominatingSet extends MinProblem[Graph, Set[Vertex]]{
//     override protected def constraints(g: Graph, k: Int) =
//       val n: Int = g.vertexSet.size
//       val esl: Seq[Edge] = g.undirected(false).edgeSet.toSeq
//       val varsX: Seq[IntConstr] = IntVar(Range(0, n))
//       val varsY: Seq[IntConstr] = IntVar(esl)
//       val varsZ: Seq[IntConstr] = IntVar(esl.flatMap(e => Range(0, g.vertexSet.size).map(v => s"${e},${v}")))
//       val vars: Seq[IntConstr] = varsX ++ varsY ++ varsZ

//       val cst1: BoolConstr = And((for (v1 <- 0 until g.vertexSet.size) yield Add(IntVar((g.adjList(v1) + v1).toList)) >= 1).toList)
//       val cst2: BoolConstr = vars >= 0 && vars <= 1 && Add(varsX) === k
//       val cst3a: BoolConstr = Add(varsY) === (Add(varsX) - 1)
//       val cst3b: BoolConstr = And(for(e <- esl) yield (IntVar(e) <= IntVar(e._1)) && (IntVar(e) <= IntVar(e._2)))
//       val cst3c: BoolConstr = And(for(e <- esl; v <- 0 until n) yield IntVar(s"${e},${v}") <= IntVar(e) && IntVar(s"${e},${v}") <= IntVar(v))
//       val cst3d: BoolConstr = And(for((i, j) <- esl; v <- 0 until n) yield IntVar(s"${(j, i)},${v}") <= IntVar((i, j)) && IntVar(s"${(j, i)},${v}") <= IntVar(v))
//       val cst3e: BoolConstr = And(for(e <- esl; v <- 0 until n) yield 
//         ((IntVar(e) - 3 + IntVar(e._1) + IntVar(e._2) + IntVar(v)) <= (IntVar(s"${e},${v}") + IntVar(s"${(e._2, e._1)},${v}"))) &&
//         ((IntVar(s"${e},${v}") + IntVar(s"${(e._2, e._1)},${v}")) <= (IntVar(e) + 3 - IntVar(e._1) - IntVar(e._2) - IntVar(v))))
//       val cst3f: BoolConstr = And(for(e <- esl) yield 
//         ((IntVar(e._1) + IntVar(e._2) - 1) <= (Add(for(k0 <- 0 until n; if k0 != e._1 && k0 != e._2) yield IntVar(s"${(e._1, k0)}${e._2}")) + IntVar(e))) &&
//         ((Add(for(k0 <- 0 until n; if k0 != e._1 && k0 != e._2) yield IntVar(s"${(e._1, k0)}${e._2}")) + IntVar(e)) <= (3 - IntVar(e._1) + IntVar(e._2))))
      
//       cst1 && cst2 && cst3a && cst3b && cst3c && cst3d && cst3e && cst3f
//     override protected def convert(g: Graph, k: Int, sol: NumQuery) = sol.filterVar(g.vertexSet.map(_.toString)).toInt.filterIdx
//     override def verify(g: Graph, k: Int, sol: Set[Vertex]) = isDominating(g, sol) && g.induced(sol).connected && sol.size == k
//     override def min(g: Graph) = min(g, g.vertexSet.size, 1)
//   }

//   object IndependentDominatingSet extends MinProblem[Graph, Set[Vertex]] {
//     override protected def constraints(g: Graph, k: Int) =
//       val vars: Seq[IntConstr] = IntVar(g.vertexSet.toSeq)
//       val cst1: BoolConstr = And((for (v1 <- 0 until g.vertexSet.size) yield Add(IntVar((g.adjList(v1) + v1).toList)) >= 1).toList)
//       val cst2: BoolConstr = vars >= 0 && Add(vars) === k
//       val cst3: BoolConstr = And((for (v1, v2) <- g.edgeSet yield IntVar(v1) + IntVar(v2) <= 1).toList)
//       cst1 && cst2 && cst3
//     override protected def convert(g: Graph, k: Int, sol: NumQuery) = sol.toInt.filterIdx
//     override def verify(g: Graph, k: Int, sol: Set[Vertex]) = isDominating(g, sol) && g.induced(sol).isIndependent && sol.size == k
//     override def min(g: Graph): Option[Set[Vertex]] = min(g, g.vertexSet.size, 1)
//   }

//   object AsymetricTravelingSalesperson extends BiProblem[Graph, Int, Set[Edge]]{
//     override protected def constraints(g: Graph, d: Int) =
//       if(g.vertexSet.size > 2 && g.connected)
//         tspConstraints(g)(d)
//       else false
//     override protected def convert(g: Graph, d: Int, sol: NumQuery) = sol.toInt.filterPairIdx
//     override def verify(g: Graph, d: Int, sol: Set[Edge]) = ???
//   }

//   object SymetricTravelingSalesperson extends BasicBiProblem[Graph, Int, Set[Edge]]{
//     override def search(g: Graph, d: Int) = AsymetricTravelingSalesperson.search(g.undirected(true), d)
//     override def decide(g: Graph, d: Int) = AsymetricTravelingSalesperson.decide(g.undirected(true), d)
//     override def enumerate(g: Graph, d: Int) = AsymetricTravelingSalesperson.enumerate(g.undirected(true), d)
//     override def verify(g: Graph, d: Int, sol: Set[Edge]) = ???

//   }

//   object DirectedHamiltonianCycle extends BasicProblem[Graph, Set[Edge]]{
//     override def search(g: Graph) = AsymetricTravelingSalesperson.search(g.unweighted, g.vertexSet.size)
//     override def decide(g: Graph) = AsymetricTravelingSalesperson.decide(g.unweighted, g.vertexSet.size)
//     override def enumerate(g: Graph) = AsymetricTravelingSalesperson.enumerate(g.unweighted, g.vertexSet.size)
//     override def verify(g: Graph, sol: Set[Edge]) = ???

//   }
  
//   object UndirectedHamiltonianCycle extends BasicProblem[Graph, Set[Edge]]{
//     override def search(g: Graph) = DirectedHamiltonianCycle.search(g.undirected(true))
//     override def decide(g: Graph) = DirectedHamiltonianCycle.decide(g.undirected(true))
//     override def enumerate(g: Graph) = DirectedHamiltonianCycle.enumerate(g.undirected(true))
//     override def verify(g: Graph, sol: Set[Edge]) = ???

//   }
  
//   object DirectedHamiltonianPath extends BasicProblem[Graph, Set[Edge]]{
//     override def search(g: Graph) = 
//       val n: Int = g.vertexSet.size
//       val nG: Graph = Graph(Matrix.fromBlock(g.adjMat, IntMatrix.ones(n, 1), IntMatrix.ones(1, n), IntMatrix.zeros(1, 1)))
//       val p = DirectedHamiltonianCycle.search(nG).map(_.filter(p => p._1 < n && p._2 < n))
//       p.map(some => if(some.size == n) some.tail else some)
//     override def decide(g: Graph) = search(g).isDefined
//     override def enumerate(g: Graph) = 
//       val n: Int = g.vertexSet.size
//       val nG: Graph = Graph(Matrix.fromBlock(g.adjMat, IntMatrix.ones(n, 1), IntMatrix.ones(1, n), IntMatrix.zeros(1, 1)))
//       val p = DirectedHamiltonianCycle.enumerate(nG).map(_.filter(p => p._1 < n && p._2 < n))
//       p.map(some => if(some.size == n) some.tail else some)
//     override def verify(g: Graph, sol: Set[Edge]) = ???
//   }
  
//   object UndirectedHamiltonianPath extends BasicProblem[Graph, Set[Edge]]{    
//     override def search(g: Graph) = DirectedHamiltonianPath.search(g.undirected(true))
//     override def decide(g: Graph) = DirectedHamiltonianPath.decide(g.undirected(true))
//     override def enumerate(g: Graph) = DirectedHamiltonianPath.enumerate(g.undirected(true))
//     override def verify(g: Graph, sol: Set[Edge]) = ???

//   }

//   object DirectedHamiltonianFixedPath extends TriProblem[Graph, Vertex, Vertex, Set[Edge]]{
//     override protected def constraints(g: Graph, start: Vertex, end: Vertex) =
//       if(g.connected)
//         val n: Int = g.vertexSet.size
//         val nG: Graph = Graph(Matrix.fromBlock(g.adjMat, IntMatrix.ones(n, 1), IntMatrix.ones(1, n), IntMatrix.zeros(1, 1)))
//         val cstStart: BoolConstr = IntVar((n, start)) === 1
//         val cstEnd: BoolConstr = IntVar((end, n)) === 1
//         tspConstraints(nG)(n + 1) && cstStart && cstEnd
//       else false
//     override protected def convert(g: Graph, start: Vertex, end: Vertex, sol: NumQuery) =
//       val n: Int = g.vertexSet.size
//       val nG: Graph = Graph(Matrix.fromBlock(g.adjMat, IntMatrix.ones(n, 1), IntMatrix.ones(1, n), IntMatrix.zeros(1, 1)))
//       sol.toInt.filterPairIdx - ((n, start)) - ((end, n))
//     override def verify(g: Graph, start: Vertex, end: Vertex, sol: Set[Edge]) = ???
//   }
  
//   object UndirectedHamiltonianFixedPath extends BasicTriProblem[Graph, Vertex, Vertex, Set[Edge]]{    
//     override def search(g: Graph, start: Vertex, end: Vertex) = DirectedHamiltonianFixedPath.search(g.undirected(true), start, end)
//     override def decide(g: Graph, start: Vertex, end: Vertex) = DirectedHamiltonianFixedPath.decide(g.undirected(true), start, end)
//     override def enumerate(g: Graph, start: Vertex, end: Vertex) = DirectedHamiltonianFixedPath.enumerate(g.undirected(true), start, end)
//     override def verify(g: Graph, start: Vertex, end: Vertex, sol: Set[Edge]) = ???
//   }
  
// /***********************Constraints***********************/
//   private def tspConstraints(g: Graph)(d: Int): BoolConstr = 
//       val vars: Seq[IntConstr] = IntVar(g.edgeSet.toSeq)
//       val cst1: BoolConstr = And(g.adjList.map((v1, se) => Add(se.map(v2 => IntVar((v1, v2))).toList) === 1).toList)
//       val cst2: BoolConstr = And(g.inNeighb.map((v2, se) => Add(se.map(v1 => IntVar((v1, v2))).toList) === 1).toList)
//       val cst3: BoolConstr = vars >= 0 && vars <= 1
//       val cst4: BoolConstr = Add(g.edgeSet.toSeq.map(e => IntVar(e) * g.wMap(e))) <= d
//       return cst1 && cst2 && cst3 && cst4
// }