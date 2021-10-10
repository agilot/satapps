package satapps

import org.scalatest.funsuite.AnyFunSuite
import scala.language.implicitConversions

 class CNFSATTest extends AnyFunSuite{
   test("units") {
     val v = "p" & ("q" | "k")
     assert(v.isCNF)
     val u = CNFSAT.units(v)
     assert(u(Variable("p")) == T)
     assert(u.size == 1)
   }

   test("remove units"){
     val v = !"q" & ("p" | "q") & (!"p" | !"k")
     assert(v.isCNF)
     val (exp, m) = CNFSAT.removeUnits(v)
     assert(exp == T)
     assert(m.size == 3)
     assert(m(Variable("q")) == F)
     assert(m(Variable("p")) == T)
     assert(m(Variable("k")) == F)
   }

   test("solve sat DPLL"){
     val v = "q" &  "p"
     assert(v.isCNF)
     val (env, res) = CNFSAT.solveSAT(v, DPLL)
     assert(env.size <= 2)
     assert(v.eval(env) == T)
     assert(res == SAT)

     val v2 = "q" &  ("p" | !"q")
     assert(v2.isCNF)
     val (env2, res2) = CNFSAT.solveSAT(v2, DPLL)
     assert(env2.size <= 2)
     assert(v2.eval(env2) == T)
     assert(res2 == SAT)

     val v3 = ("p" | "q") & "r"
     assert(v3.isCNF)
     val (env3, res3) = CNFSAT.solveSAT(v3, DPLL)
     assert(env3.size <= 3)
     assert(v3.eval(env3) == T)
     assert(res3 == SAT)
   }
 }
