package satapps

import problems.Languages.CloseString
import scala.util.Random
import org.scalatest.funsuite.AnyFunSuite

class LanguageTest extends AnyFunSuite{
  test("CloseString") {
    trait Solver extends CloseString {
      override type Char = scala.Char
      override def distance(lhs: Char, rhs: Char): Int = if lhs == rhs then 0 else 1
    }

    def testCase(expected: Option[String], k: Int, strings: String*)(using instance: Solver): Unit = {
      require(!instance.alphabet.contains('_'))
      val strs = strings.toSeq.map(_.toSeq)
      val result = instance.solve(strs, k)

      (expected, result) match {
        case (None, None) => ()
        case (Some(sol), None) => fail(s"Expected solution \"${sol.mkString}\" was not found.")
        case (None, Some(res)) => fail(s"Unexpected solution \"${res.mkString}\" found.")
        case (Some(sol), Some(res)) => {
          assert(sol.length == res.length, s"Length mismatch between \"${sol.mkString}\" and \"${res.mkString}\"")

          for (s, r) <- sol.zip(res) do 
            if(s != '_')
              assert(s == r, s"Character mismatch between \"${sol.mkString}\" and \"${res.mkString}\"")

          assert(instance.verify(res, strs, k), "Produces solution should be valid.")
        }
      }
    }

    def solvable(expected: String, k: Int, strs: String*)(using instance: Solver): Unit = 
      testCase(Some(expected), k, strs: _*)

    def unsolvable(k: Int, strs: String*)(using instance: Solver): Unit = 
      testCase(None, k, strs: _*)

    def offsetRandomly(s: Seq[Char], d: Int)(using instance: Solver): Seq[Char] = {
      require(instance.alphabet.size > 1)
      require(d <= s.length)

      def randomChar: Char = {
        val idx = Random.nextInt(instance.orderedAlphabet.length)
        instance.orderedAlphabet(idx)
      }

      def otherChar(char: Char): Char = {
        val c = randomChar
        if char == c then otherChar(char) else c
      }.ensuring(res => res != char)

      val indices = Random.shuffle(0 until s.length).take(d)
      indices.foldLeft(s)( (s, i) => s.updated(i, otherChar(s(i))) )
    }.ensuring(res => res.length == s.length && instance.distance(res, s) == d)

    // Simple instances
    {
      given Solver with
        lazy val alphabet = Set('a', 'b', 'c')

      solvable("abc", 0, "abc")
      solvable("a_c", 1, "aac", "abc", "acc")
      solvable("abc", 1, "aac", "aba", "bbc")
      unsolvable(1, "aac", "aba", "bcc")
    }

    // Random instances
    for _ <- 0 until 3 do {
      val len = 37

      given solver: Solver with
        lazy val alphabet = ( ('A' to 'Z') ++ ('a' to 'z') ++ ('0' to '9') ).toSet

      val base = Random.alphanumeric.take(len)
      val k = 11

      val strs = Random.integers(k).take(23).map(d => offsetRandomly(base, d).mkString)
      
      assert(solver.verify(base, strs.map(_.toSeq), k))

      solvable("_" * len, k, strs: _*)
    }

    for _ <- 0 until 3 do {
      val len = 37

      given solver: Solver with
        lazy val alphabet = ( ('A' to 'Z') ++ ('a' to 'z') ++ ('0' to '9') ).toSet

      val base = Random.alphanumeric.take(len)
      val k = 11

      val leeway = math.ceil(k/10).toInt
      val maxOffset = 2*k + leeway

      val strs = 
        base.mkString ::
        ( (Random.nextInt(leeway) + 2*k + 1) :: Random.integers(maxOffset).take(23).toList )
          .map(d => offsetRandomly(base, d).mkString)

      unsolvable(k, strs: _*)
    }
  }
}