package satapps

import org.scalatest.matchers.should._
import org.scalatest.propspec.AnyPropSpec
import org.scalatest.prop._
import org.scalatest.GivenWhenThen

class MatrixTests
    extends AnyPropSpec
    with TableDrivenPropertyChecks
    with Matchers
    with GivenWhenThen {

  def sameType[T, U](a: T, b: U)(implicit evidence: T =:= U) = true


  val fixedMat =
    Table(
      "fixedMat",
      // 0
      Matrix(Seq(1), 1, 1),
      // 1
      Matrix(Seq(1, 0, 0, 1), 2, 2),
      // 2
      Matrix(Seq(3, 3, 3, 3, 3, 3), 2, 3),
      // 3
      Matrix(Seq(1, 2, 3, 4, 5, 6, 7, 8), 1, 8),
      // 4
      Matrix(Seq(true, true, false, true, false, false), 3, 2),
      // 5
      Matrix(
        Seq(
          Matrix(Seq(1, 2, 3, 4, 5, 6), 2, 3),
          Matrix(Seq(7, 8, 9), 3, 1),
          Matrix(Seq(10, 11), 1, 2),
          Matrix(Seq(12, 13, 14, 15), 2, 2)
        ),
        2,
        2
      )
    )

  property("size should be the product of the shape") {
    forAll(fixedMat) { m => m.shape._1 * m.shape._2 shouldBe m.size }
  }

  property("size of transpose should not change") {
    forAll(fixedMat) { m => m.T.size shouldBe m.size }
  }

  property("size of vstack should be the sum of the sizes") {
    forAll(fixedMat) { m1 =>
      forAll(fixedMat) { m2 =>
        whenever(m1.columns == m2.columns) {
          (m1 vstack m2).size shouldBe (m1.size + m2.size)
        }
      }
    }
  }

  property("size of hstack should be the sum of the sizes") {
    forAll(fixedMat) { m1 =>
      forAll(fixedMat) { m2 =>
        whenever(m1.rows == m2.rows) {
          (m1 hstack m2).size shouldBe (m1.size + m2.size)
        }
      }
    }
  }

  property("size of reshape should be the same") {
    forAll(fixedMat) { m => m.reshape(m.columns, m.rows).size shouldBe m.size }
  }

  property("size of flatten should be the size") {
    forAll(fixedMat) { m => m.flatten.size shouldBe m.size }
  }

  property("size should be the product between rows and columns") {
    forAll(fixedMat) { m => m.size shouldBe m.columns * m.rows }
  }

  property("equals reflexivity") {
    forAll(fixedMat) {m => m shouldEqual m}
  }


  // test("apply") {
  //   for (v <- 0 until 6) {
  //     val i = v / 3
  //     val j = v % 3
  //     assert(m(i, j) == (v + 1))
  //   }
  // }

  // test("toString") {
  //   assert(
  //     m.toString
  //       ==
  //         "1 2 3\n4 5 6"
  //   )
  // }

  // test("equals") {
  //   assert(m == m)
  //   assert(m == s)
  //   assert(m != o)
  //   assert(m != t)
  // }

  // test("Horizontal concatenation") {
  //   assert(
  //     m.hstack(o)
  //       ==
  //         Matrix(
  //           Seq(1, 2, 3, 1, 2, 4),
  //           Seq(4, 5, 6, 4, 5, 6)
  //         )
  //   )
  // }

  // test("Vertical concatenation") {
  //   assert(
  //     m.vstack(o)
  //       ==
  //         Matrix(
  //           Seq(1, 2, 3),
  //           Seq(4, 5, 6),
  //           Seq(1, 2, 4),
  //           Seq(4, 5, 6)
  //         )
  //   )
  // }
}
