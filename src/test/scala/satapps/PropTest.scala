// package satapps
// import org.scalatest.funsuite.AnyFunSuite
// import scala.language.implicitConversions

//  class PropTest extends AnyFunSuite{
//    test("eval"){
//      val v = !"q" & ("p" | "q") & (!"p" | !"k")
//      assert(v.isCNF)
//      val v1 = "p"  & (!"p" | !"k")
//      assert(v.eval(Map(Variable("q") -> F)) == v1)
//      assert(v.eval(Map(Variable("q") -> F, Variable("p") -> T, Variable("k") -> F)) == T)
//      val w = ("p" | "q") & "r"
//      assert(w.eval(Map(Variable("r") -> T, Variable("p") -> T)) == T)
//    }

//    test("at most k"){
//     def atMostTest(n: Int, k: Int) = 
//       val l = (for(i <- 0 until n) yield Variable(s"x${i}")).toList
//       val alk = Prop.atMostK(l, k)
//       assert(alk.isCNF)
//       def m(j: Int) = (for(i <- 0 until n) yield if (i < j) Variable(s"x${i}") -> T  else Variable(s"x${i}") -> F).toMap
//       def t(j: Int): SATResult = CNFSAT.solveSAT(alk.eval(m(j)), DPLL)._2
//       (for(j <- 0 to n) yield 
//         val tj: SATResult = t(j)
//         if(j > k) tj == UNSAT else tj == SAT).toList.forall(_ == true)
//     for(n <- 1 to 10; k <- 0 to n) 
//       assert(atMostTest(n, k))
//    }

//    test("at least k"){
//     def atLeastTest(n: Int, k: Int) = 
//       val l = (for(i <- 0 until n) yield Variable(s"x${i}")).toList
//       val alk = Prop.atLeastK(l, k)
//       assert(alk.isCNF)
//       def m(j: Int) = (for(i <- 0 until n) yield if (i < j) Variable(s"x${i}") -> T  else Variable(s"x${i}") -> F).toMap
//       def t(j: Int): SATResult = CNFSAT.solveSAT(alk.eval(m(j)), DPLL)._2
//       (for(j <- 0 to n) yield 
//         val tj: SATResult = t(j)
//         if(j < k) tj == UNSAT else tj == SAT).toList.forall(_ == true)
//     for(n <- 1 to 10; k <- 0 to n)
//       assert(atLeastTest(n, k))
//    }

//    test("exactly 1"){
//     def exOneTest(n: Int) = 
//       val l = (for(i <- 0 until n) yield Variable(s"x${i}")).toList
//       val alk = Prop.exactlyOne(l)
//       assert(alk.isCNF)
//       def m(j: Int) = (for(i <- 0 until n) yield if (i < j) Variable(s"x${i}") -> T  else Variable(s"x${i}") -> F).toMap
//       def t(j: Int): SATResult = CNFSAT.solveSAT(alk.eval(m(j)), DPLL)._2
//       (for(j <- 0 to n) yield 
//         val tj: SATResult = t(j)
//         if(j == 1) tj == SAT else tj == UNSAT).toList.forall(_ == true)
//     for(n <- 1 to 10)
//       assert(exOneTest(n))
//    }
//  }
