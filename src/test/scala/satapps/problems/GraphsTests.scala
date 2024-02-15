// package satapps.problems

// import satapps.*
// // import Graphs.*
// // import Graph.*

// import org.scalatest.funsuite.AnyFunSuite
// import scala.util.Random

// class GraphsTests extends AnyFunSuite{
//   val rng = Random(100)
//   def randomGraph(n: Int) = 
//     Graph(Range(0, n).toSet, (for(i <- 0 until n; j <- 0 until n if i != j) yield ((i, j), rng.nextBoolean())).filter(_._2).map(_._1).toSet)

//   test("Independent Set"){
//     val n = 5
//     val r = 10
//     for(i <- 1 until n)
//       for(j <- 1 to i)
//         assert((j == 1) == Indset.decide(complete(i), j))
//         assert(Indset.decide(empty(i), j))
//         for(k <- 1 to r)
//           val rg = randomGraph(i)
//           assert(Indset.search(rg, j) match {
//             case Some(sol) => Indset.verify(rg, j, sol)
//             case None => true
//             }
//           )
//   }

//   test("Dominating Set"){
//     val n = 5
//     val r = 10
//     for(i <- 1 until n)
//       for(j <- 1 to i)
//         assert(DominatingSet.decide(complete(i), j))
//         assert((i == j) == DominatingSet.decide(empty(i), j))
//         for(k <- 1 to r)
//           val rg = randomGraph(i)
//           assert(DominatingSet.search(rg, j) match {
//             case Some(sol) => DominatingSet.verify(rg, j, sol)
//             case None => true
//             }
//           )
//   }



//   test("hamiltonian"){
//     // println(Graphs.complete(5).hamiltonianCycle)
//     // println(Graphs.complete(5).hamiltonianPath)

//     // println(Graph(Set(0, 1, 2), Set((0, 1), (1, 0), (1, 2), (2, 1))).hamiltonianCycle)
//     // println(Graph(Set(0, 1, 2), Set((0, 1), (1, 0), (1, 2), (2, 1))).hamiltonianPath)
//     val g =Graph(Set(0, 1, 2, 3, 4, 5, 6), Set((0, 1), (0, 3), (0, 5), (1, 0), (1, 2), (2, 3), (2, 6), (2, 1), (3, 0), (3, 2), (3, 4), (3, 5), (3, 6), (4, 3), (4, 6), (5, 0), (5, 3), (5, 6), (6, 5), (6, 3), (6, 2), (6, 4)))
//     //println(hamiltonianCycle(g))
//   }


// }