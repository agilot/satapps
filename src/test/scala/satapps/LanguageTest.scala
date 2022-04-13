package satapps

import org.scalatest.funsuite.AnyFunSuite

class LanguageTest extends AnyFunSuite{
  test("CloseString") {
    object Solver extends CloseString {
      override type Char = scala.Char
    }

    def testCase(expected: Option[String], alphabet: String, k: Int, strs: String*): Unit = {
      assert(!alphabet.contains("_"))
      val result = Solver.solve(strs.toSeq.map(_.toSeq), alphabet.toSet, k)

      (expected, result) match {
        case (None, None) => ()
        case (Some(sol), None) => fail(s"Expected solution \"${sol}\" was not found.")
        case (None, Some(res)) => fail(s"Unexpected solution \"${res}\" found.")
        case (Some(sol), Some(res)) => {
          assert(sol.length == res.length, s"Length mismatch between \"${sol}\" and \"${res}\"")

          for (s, r) <- sol.zip(res) do 
            if(s != '_')
              assert(s == r, s"Character mismatch between \"${sol}\" and \"${res}\"")
        }
      }
    }

    def solvable(expected: String, alphabet: String, k: Int, strs: String*): Unit = 
      testCase(Some(expected), alphabet, k, strs: _*)


    def unsolvable(alphabet: String, k: Int, strs: String*): Unit = 
      testCase(None, alphabet, k, strs: _*)

    solvable("abc", "abc", 0, "abc")
    solvable("a_c", "abc", 1, "aac", "abc", "acc")
    solvable("abc", "abc", 1, "aac", "aba", "bbc")
    unsolvable("abc", 1, "aac", "aba", "bcc")
  }
}