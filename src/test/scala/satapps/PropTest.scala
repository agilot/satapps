package satapps
import org.scalatest.funsuite.AnyFunSuite
import scala.language.implicitConversions

 class PropTest extends AnyFunSuite{
   test("eval"){
     val v = !"q" & ("p" | "q") & (!"p" | !"k")
     assert(v.isCNF)
     val v1 = "p"  & (!"p" | !"k")
     assert(v.eval(Map(Variable("q") -> F)) == v1)
     assert(v.eval(Map(Variable("q") -> F, Variable("p") -> T, Variable("k") -> F)) == T)
     val w = ("p" | "q") & "r"
     assert(w.eval(Map(Variable("r") -> T, Variable("p") -> T)) == T)
   }
 }
