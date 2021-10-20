package satapps
import scala.collection.mutable.ArrayBuffer

import scala.language.implicitConversions

object Main{

  def xorMat(a: BinaryMatrix, b: BinaryMatrix): Boolean = 
    def matToCNF(mat: BinaryMatrix): Expr = 
      Prop.xor2ClauseToCNF((for(i <- 0 until mat.r; j <- 0 until mat.c)
        yield if (mat(i,j)) Not(Xor(Variable(s"r${i}"), Variable(s"c${j}"))) else Xor(Variable(s"r${i}"), Variable(s"c${j}"))
      ).reduce(And(_, _)))
    
    TwoSAT.solve2SAT(matToCNF(a.xor(b))) == SAT

  def main(args: Array[String]): Unit = {
      val s = ImMultiSet(Map(1 -> 1, 2 -> 2, 3 -> 3))
      val t = ImMultiSet(Map(1 -> 1, 2 -> 1, 3 -> 2, 4 -> 1))
      println(s.inter(t))
      println(s.filter(_ >= 3))
      //val graph = GraphFromEdgeSet(Set(0, 1, 2, 3), Set((0, 1), (1, 2), (2, 3), (0, 3)))
      //val graph2 = GraphFromEdgeSet(Set(0, 1, 2), Set((0, 1), (1, 0), (2, 1), (1, 2), (0, 2), (2, 0)))
      //println(graph.graphColoring(4, DPLL))
      //println(graph2.clique(3, DPLL))
      //println(graph.bfs(0))
      //println(CNFSAT.removeAux(CNFSAT.solveSAT((("p" | "q") & "r").toCNF, DPLL)._1))
      //println(CNFSAT.solveSAT(!Variable("q") | Variable("q") & Variable("p"), BruteForce))
      //println(Prop.exactlyOne(Variable("a") :: Variable("b") :: Variable("c") :: Nil))
  }
}