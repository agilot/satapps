package satapps
import scala.collection.mutable.ArrayBuffer

import scala.language.implicitConversions

object Main{

  // def xorMat(a: BinaryMatrix, b: BinaryMatrix): Boolean = 
  //   def matToCNF(mat: BinaryMatrix): Expr = 
  //     Prop.xor2ClauseToCNF((for(i <- 0 until mat.rows; j <- 0 until mat.cols)
  //       yield if (mat(i,j)) Not(Xor(Variable(s"r${i}"), Variable(s"c${j}"))) else Xor(Variable(s"r${i}"), Variable(s"c${j}"))
  //     ).reduce(And(_, _)))
    
  //   TwoSAT.solve2SAT(matToCNF(a ^ b)) == SAT

  def main(args: Array[String]): Unit = {
      //println(Mat.sudoku(3, DPLL, Nil))
      //println(Mat.nQueens(4, DPLL, Nil))
      //println(Circuits.subsetSum(List(2, 3, 5, 7), 6, DPLL))
      //val s = ImMultiSet(Map(1 -> 1, 2 -> 2, 3 -> 3))
      //println(SetRed.setPacking(4, Set(Set(1, 2, 3), Set(4, 5, 6), Set(2, 4), Set(1, 7), Set(2, 3)), DPLL))
      //println(SetRed.setCover(3, Set(1, 2, 3, 4, 5, 6, 7), List(Set(1, 2, 3), Set(4, 5, 6), Set(2, 4), Set(1, 7), Set(2, 3))))
      //println(SetRed.nPartition(MultiSetFactory.from(Seq(10, 8, 2, 2, 11, 1, 6, 4, 7, 6, 5, 4)), 4))
      //val t = ImMultiSet(Map(1 -> 1, 2 -> 1, 3 -> 2, 4 -> 1))
      //val graph = GraphFromEdgeSet(Set(0, 1, 2, 3), Set((0, 1), (1, 2), (2, 3), (0, 3)))
      //println(graph.vertexCover(1, DPLL))
      //val graph2 = GraphFromEdgeSet(Set(0, 1, 2), Set((0, 1), (1, 0), (2, 1), (1, 2), (0, 2), (2, 0)))
      //println(graph.graphColoring(4, DPLL))
      //println(graph2.clique(3, DPLL))
      //println(graph.bfs(0))
      //println(CNFSAT.removeAux(CNFSAT.solveSAT((("p" | "q") & "r").toCNF, DPLL)._1))
      //println(CNFSAT.solveSAT(!Variable("q") | Variable("q") & Variable("p"), BruteForce))
      //println(Prop.exactlyOne(Variable("a") :: Variable("b") :: Variable("c") :: Nil))
  }
}