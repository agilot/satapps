package satapps.problems

import satapps.*
import Z3.{*, given}
import Extensions.*

object Languages {
  trait CloseString {
    // Problem abstraction
    type Char
    type Str = Seq[Char]

    lazy val alphabet: Set[Char]

    def distance(lhs: Char, rhs: Char): Int

    // Utils
    lazy val orderedAlphabet = alphabet.toSeq

    final def checkInstance(strs: Seq[Str], k: Int): Int = {
      assert(!strs.isEmpty, "A Str must be provided")
      val len = strs(0).length

      assert(0 <= k && k <= len, s"k (${k}) is out of bounds (${0}, ${len})")

      for str <- strs do 
        assert(str.length == len, s"\"${str}\".length != ${len}")

      for str <- strs 
          char  <- str     do
        assert(alphabet.contains(char), s"Unexpected char: ${char}")

      len
    }

    final def distance(lhs: Str, rhs: Str): Int = {
      require(lhs.length == rhs.length)
      lhs.zip(rhs).map( (l, r) => distance(l, r) ).reduce(_ + _)
    }.ensuring(_ >= 0)

    // Problem methods
    final def solve(strs: Seq[Str], k: Int): Option[Seq[Char]] = {
      val len = checkInstance(strs, k)
      
      val charIdx = alphabet.zipWithIndex.toMap

      // Index X Value
      val varsName = (0 until len).map(i => 
          orderedAlphabet.map(j => s"x[${i},${j}]")
        )
      val vars = varsName.map(_.map(intConst(_)))
      
      val varsMap = (idx: Int, char: Char) => vars(idx)(charIdx(char))

      val positiveCstrs = vars.flatten.map(_ >= 0)
      val choiceCstrs = vars.map(choice => sum(choice) === 1)
      val distanceCstrs = strs.map(str =>  {
        val terms = for i <- 0 until len; char <- alphabet
          yield distance(str(i), char) * varsMap(i, char)

        sum(terms) <= k
      })

      val prog = andAll(positiveCstrs ++ choiceCstrs ++ distanceCstrs)
      val (trees, ctx) = Z3.solve(prog, varsName.flatten)


      val sol = trees.map(ls => {
        assert(ls.length == varsName.flatten.length)
        assert(len * orderedAlphabet.length == varsName.flatten.length)

        ls.grouped(orderedAlphabet.length).map(seqIdx => {
          assert(seqIdx.length == orderedAlphabet.length)
          val idx = seqIdx.zipWithIndex.collectFirst{ case (v, i) if toInt(v) > 0 => i }.get
          orderedAlphabet(idx)
        }).toSeq
      })

      ctx.delete()
      sol
    }

    final def decide(strs: Seq[Str], k: Int): Boolean = solve(strs, k).isDefined

    final def verify(query: Str, strs: Seq[Str], k: Int): Boolean = {
      val len = checkInstance(strs, k)

      query.length == len && strs.forall(str => distance(query, str) <= k)
    }
  }
}