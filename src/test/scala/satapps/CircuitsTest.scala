package satapps
import org.scalatest.funsuite.AnyFunSuite
import scala.language.implicitConversions
import Circuits._

class CircuitsTest extends AnyFunSuite{
  val x = List(Constant(false), Constant(false), Constant(true))
  val y = List(Constant(false), Constant(true), Constant(true))

  test("adder"){
    assert(intAdder(x, y).map(_.apply(Map())) == List(true, false, false))
  }

  test("eq"){
    
    assert(bitwiseEq(x, y).map(_.apply(Map())) == List(true, false, true))
    assert(bitwiseEq(x, x).map(_.apply(Map())) == List(true, true, true))
    assert(bitwiseEq(y, y).map(_.apply(Map())) == List(true, true, true))
  }

  test("toBinary"){
    assert(toBinary(1, 3) == x)
    assert(toBinary(3, 3) == y)
  }
}