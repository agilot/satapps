package satapps
import org.scalatest.funsuite.AnyFunSuite

class SetsTest extends AnyFunSuite{
  test("incl"){
    val set: MultiSet[Int] = MultiSet()
    val set2 = set + 1 + 1 + 2 + 3 + 4
    assert(set2.contains(1))
    assert(set2.contains(2))
    assert(set2.contains(3))
    assert(set2.contains(4))
    assert(!set2.contains(0))
    assert(!set2.contains(5))
  }
  
  test("excl"){
    val set: MultiSet[Int] = MultiSet(1 -> 1, 2 -> 2, 3 -> 3)
    val set2 = set - 1 - 2 - 3
    assert(!set2.contains(1))
    assert(set2.contains(2))
    assert(set2.contains(3))
    val set3 = set2 - 1 - 2 - 3
    assert(!set3.contains(1))
    assert(!set3.contains(2))
    assert(set3.contains(3))
    val set4 = set3 - 1 - 2 - 3
    assert(!set4.contains(1))
    assert(!set4.contains(2))
    assert(!set4.contains(3))
  }

  test("mult/apply"){
    val set: MultiSet[Int] = MultiSet(1 -> 1, 2 -> 2, 3 -> 3)
    assert(set(1) == 1 && set.mult(1) == 1)
    assert(set(2) == 2 && set.mult(2) == 2)
    assert(set(3) == 3 && set.mult(3) == 3)
    val set2 = set - 1 - 2 - 3
    assert(set2(1) == 0 && set2.mult(1) == 0)
    assert(set2(2) == 1 && set2.mult(2) == 1)
    assert(set2(3) == 2 && set2.mult(3) == 2)
    val set3 = set2 - 1 - 2 - 3
    assert(set3(1) == 0 && set3.mult(1) == 0)
    assert(set3(2) == 0 && set3.mult(2) == 0)
    assert(set3(3) == 1 && set3.mult(3) == 1)
    val set4 = set3 - 1 - 2 - 3
    assert(set4(1) == 0 && set4.mult(1) == 0)
    assert(set4(2) == 0 && set4.mult(2) == 0)
    assert(set4(3) == 0 && set4.mult(3) == 0)
  }

  test("inter"){
    val set: MultiSet[Int] = MultiSet(1 -> 1, 2 -> 2, 3 -> 3, 4 -> 4)
    val set2: MultiSet[Int] = MultiSet(0 -> 1, 1 -> 1, 2 -> 1, 3 -> 4)
    val set3 = set & set2
    assert(set3(0) == 0 && set3(1) == 1 && set3(2) == 1 && set3(3) == 3 && set3(4) == 0)
    assert(set3 == MultiSet(1 -> 1, 2 -> 1, 3 -> 3))
  }

  test("union"){
    val set: MultiSet[Int] = MultiSet(1 -> 1, 2 -> 2, 3 -> 3, 4 -> 4)
    val set2: MultiSet[Int] = MultiSet(0 -> 1, 1 -> 1, 2 -> 1, 3 -> 4)
    val set3 = set.union(set2)
    assert(set3(0) == 1 && set3(1) == 1 && set3(2) == 2 && set3(3) == 4 && set3(4) == 4)
    assert(set3 == MultiSet(0 -> 1, 1 -> 1, 2 -> 2, 3 -> 4, 4 -> 4))
  }

}