package satapps

import Z3.*

trait CloseString {
  type Char
  type Str = Seq[Char]

  def checkInstance(Strs: Seq[Str], alphabet: Set[Char], k: Int): Int = {
    assert(!Strs.isEmpty, "A Str must be provided")
    val len = Strs(0).length

    assert(0 <= k && k <= len, s"k (${k}) is out of bounds (${0}, ${len})")

    for str <- Strs do 
      assert(str.length == len, s"\"${str}\".length != ${len}")

    for str <- Strs 
        char  <- str     do
      assert(alphabet.contains(char), s"Unexpected char: ${char}")

    len
  }

  private def program(strs: Seq[Str], len: Int, alphabet: Seq[Char], k: Int): (Z3Type, Seq[String]) = {
    val charIdx = alphabet.zipWithIndex.toMap

    // Index X Value
    val varsName = (0 until len).map(i => 
        alphabet.map(j => s"x[${i},${j}]")
      )
    val vars = varsName.map(_.map(intConst(_)))
      

    val positiveCstrs = vars.flatten.map(_ >= 0)
    val choiceCstrs = vars.map(choice => sum(choice) === 1)
    val distanceCstrs = strs.map(str =>
      sum( (0 until len).map(i => vars(i)(charIdx(str(i)))) ) >= len - k
    )

    (andAll(positiveCstrs ++ choiceCstrs ++ distanceCstrs), varsName.flatten[String])
  }

  def solve(strs: Seq[Str], a: Set[Char], k: Int): Option[Seq[Char]] = {
    val alphabet = a.toSeq
    val len = checkInstance(strs, alphabet.toSet, k)
    val (prog, vars) = program(strs, len, alphabet, k)
    val (trees, ctx) = Z3.solve(prog, vars)

    val sol = trees.map(_.grouped(len).map(seqIdx => {
      val idx = seqIdx.zipWithIndex.collectFirst{ case (v, i) if toInt(v) > 0 => i }.get
      alphabet(idx)
    }).toSeq)

    ctx.delete()
    sol
  }
}