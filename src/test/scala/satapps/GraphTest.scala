package satapps
import org.scalatest.funsuite.AnyFunSuite
import scala.language.implicitConversions
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
    for(i <- 1 to n){assert(Graphs.complete(n).dominatingSet(1).isDefined)}

    for(i <- 1 to n - 1){
      assert(!Graphs.empty(n).dominatingSet(i).isDefined)
    }
  }

  test("indset/clique"){
    val n = 5
    for(i <- 2 to 5){
      assert(!Graphs.complete(n).indset(i).isDefined)
      assert(Graphs.complete(n).clique(i).isDefined)
      assert(Graphs.empty(n).indset(i).isDefined)
      assert(!Graphs.empty(n).clique(i).isDefined)
    }
  }

  test("hamiltonian"){
    println(Graphs.complete(5).hamiltonianCycle)
    println(Graphs.complete(5).hamiltonianPath)

    println(Graph(Set(0, 1, 2), Set((0, 1), (1, 0), (1, 2), (2, 1))).hamiltonianCycle)
    println(Graph(Set(0, 1, 2), Set((0, 1), (1, 0), (1, 2), (2, 1))).hamiltonianPath)
  }


}