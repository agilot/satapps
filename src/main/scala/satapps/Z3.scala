package satapps

import z3.scala.*
import scala.annotation.targetName
import Extensions.*

object Z3 {
  type Z3Type = Z3Context => Z3AST

  def sum(s: Seq[Z3Type]): Z3Type = z => z.mkAdd(s.map(elem => elem(z)): _*)
  def prod(s: Seq[Z3Type]): Z3Type = z => z.mkMul(s.map(elem => elem(z)): _*)
  def andAll(s: Seq[Z3Type]): Z3Type = z => z.mkAnd(s.map(elem => elem(z)): _*)
  def orAll(s: Seq[Z3Type]): Z3Type = z => z.mkOr(s.map(elem => elem(z)): _*)
  def distinct(s: Seq[Z3Type]): Z3Type = z => z.mkDistinct(s.map(elem => elem(z)): _*)

  def intConst(s: String): Z3Type = z => z.mkIntConst(s)
  def intConst(s: Seq[String]): Seq[Z3Type] = s.map(intConst)

  def boolConst(s: String): Z3Type = z => z.mkBoolConst(s)
  def boolConst(s: Seq[String]): Seq[Z3Type] = s.map(boolConst)

  given Conversion[Int, Z3Type] with
    def apply(id: Int) = z => z.mkInt(id, z.mkIntSort())

  given Conversion[Boolean, Z3Type] with
    def apply(id: Boolean) = z => if (id) z.mkTrue() else z.mkFalse()


  def toInt(v: Z3AST): Int = v.toString.toInt
  @targetName("toIntOption")
  def toInt(o: Option[Z3AST]): Option[Int] = o.map(toInt)
  @targetName("toIntOptionSeq")
  def toInt(os: Option[Seq[Z3AST]]): Option[Seq[Int]] = os.map(_.map(toInt))
  def toInt(s: Seq[Z3AST]): Seq[Int] = s.map(toInt)

  def toBoolean(v: Z3AST): Boolean = v.toString.toBoolean
  @targetName("toBooleanOption")
  def toBoolean(o: Option[Z3AST]): Option[Boolean] = o.map(toBoolean)
  @targetName("toBooleanOptionSeq")
  def toBoolean(os: Option[Seq[Z3AST]]): Option[Seq[Boolean]] = os.map(_.map(toBoolean))
  def toBoolean(s: Seq[Z3AST]): Seq[Boolean] = s.map(toBoolean)

  def solve(cst: Z3Type, vars: Seq[String]): (Option[Seq[Z3AST]], Z3Context) =
    val z: Z3Context = Z3Context("MODEL" -> true)
    val solv:Z3Solver = z.mkSolver()
    solv.assertCnstr(cst(z))
    val res = solv.check() match 
      case None => throw IllegalStateException("Z3 Failed")
      case Some(false) => None
      case Some(true) => 
          val mod = solv.getModel()
          Some(vars.map(mod.getConstInterpretation(_).getOrElse(throw IllegalStateException("The variable should be defined"))).toList)
    
    (res, z)

  def filterSol(sol: Option[Seq[Z3AST]]): Option[Seq[Int]] = 
    toInt(sol).map(_.zipWithIndex.filter((x, j) => x > 0).map((x, j) => j))

}