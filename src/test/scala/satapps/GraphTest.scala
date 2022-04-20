package satapps
import org.scalatest.funsuite.AnyFunSuite
import scala.language.implicitConversions
import GraphProb.*
import z3.scala.*

class GraphTest extends AnyFunSuite{
  test("empty/complete"){
    val n = 5
    for(i <- 2 to 5){
      val g1 = Graphs.complete(n)
      val g1c = g1.nonReflComplement
      val g2 = Graphs.empty(n)
      val g2c = g2.nonReflComplement
      assert(g1c.adjList == g2.adjList)
      assert(g2c.adjList == g1.adjList)
      assert(g1c.edgeSet == g2.edgeSet)
      assert(g2c.edgeSet == g1.edgeSet)
      assert(g1c.vertexSet == g2.vertexSet)
      assert(g2c.vertexSet == g1.vertexSet)
    }
  }

  test("dominating set"){
    val n = 5
    for(i <- 1 to n){assert(dominatingSet(Graphs.complete(n))(1).isDefined)}

    for(i <- 1 to n - 1){
      assert(!dominatingSet(Graphs.empty(n))(i).isDefined)
    }
  }

  test("indset/clique"){
    val n = 5
    for(i <- 2 to 5){
      assert(!indset(Graphs.complete(n))(i).isDefined)
      assert(clique(Graphs.complete(n))(i).isDefined)
      assert(indset(Graphs.empty(n))(i).isDefined)
      assert(!clique(Graphs.empty(n))(i).isDefined)
    }
  }

  test("hamiltonian"){
    // println(Graphs.complete(5).hamiltonianCycle)
    // println(Graphs.complete(5).hamiltonianPath)

    // println(Graph(Set(0, 1, 2), Set((0, 1), (1, 0), (1, 2), (2, 1))).hamiltonianCycle)
    // println(Graph(Set(0, 1, 2), Set((0, 1), (1, 0), (1, 2), (2, 1))).hamiltonianPath)
    val g =Graph(Set(0, 1, 2, 3, 4, 5, 6), Set((0, 1), (0, 3), (0, 5), (1, 0), (1, 2), (2, 3), (2, 6), (2, 1), (3, 0), (3, 2), (3, 4), (3, 5), (3, 6), (4, 3), (4, 6), (5, 0), (5, 3), (5, 6), (6, 5), (6, 3), (6, 2), (6, 4)))
    println(hamiltonianCycle(g))
  }


}