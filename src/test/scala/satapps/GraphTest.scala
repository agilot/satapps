package satapps
import org.scalatest.funsuite.AnyFunSuite
import scala.language.implicitConversions

class GraphTest extends AnyFunSuite{
  test("clique"){
    val n = 5
    for(i <- 2 to 5){
      assert(Graphs.complete(n, Graphs.FromEdgeSet).clique(i, DPLL))
      assert(!Graphs.complete(n, Graphs.FromEdgeSet).complement.clique(i, DPLL)) 
    }

    for(i <- 2 to 5){
      assert(Graphs.empty(n, Graphs.FromEdgeSet).complement.clique(i, DPLL))
      assert(!Graphs.empty(n, Graphs.FromEdgeSet).clique(i, DPLL))
    }
  }

  test("indset"){
    val n = 5
    for(i <- 2 to 5){
      println(Graphs.complete(n, Graphs.FromEdgeSet).complement.edgeSet)
      assert(!Graphs.complete(n, Graphs.FromEdgeSet).indset(i, DPLL))  
    }

    for(i <- 2 to 5){
      assert(Graphs.empty(n, Graphs.FromEdgeSet).indset(i, DPLL))
    }
  }
}