package satapps

import z3.scala.*
import z3.scala.Z3AST
import scala.annotation.targetName
import scala.collection.immutable.Stream.Cons


object ConstrProg{

  protected class Query[T](private val mapping: Map[String, T]){
    def query(i: Iterable[String]): Iterable[T] = i.map(mapping(_))
    def map[U](f: ((String, T)) => U): Iterable[U] = mapping.map(f) 
    def filterVar(p: String => Boolean): Query[T] = Query(mapping.filterKeys(p).toMap)
    def filterVar(i: Seq[String]): Query[T] = filterVar(i.toSet)
    def filterVal(p: T => Boolean): Query[T] = Query(mapping.filter((_, c) => p(c)))
    def varSet: Set[String] = mapping.keySet
    override def toString(): String = mapping.toString
  }

  type NumQuery = Query[Const]
  type IntQuery = Query[Int]

  def IntQuery(mapping: Map[String, Int]) = Query[Int](mapping)
  def NumQuery(mapping: Map[String, Const]) = Query[Const](mapping)

  sealed trait Constr{

    protected def vars: Set[Var] =
      this match{
        case Add(ops*) => ops.map(_.vars).foldLeft(Set())(_ ++ _)
        case Sub(op1, op2) => op1.vars ++ op2.vars
        case Mul(ops*) => ops.map(_.vars).foldLeft(Set())(_ ++ _)
        case c: Const => Set()
        case v: Var => Set(v)
        case And(ops*) => ops.map(_.vars).foldLeft(Set())(_ ++ _)
        case Or(ops*) => ops.map(_.vars).foldLeft(Set())(_ ++ _)
        case Xor(op1, op2) => op1.vars ++ op2.vars
        case Iff(op1, op2) => op1.vars ++ op2.vars
        case Not(op) => op.vars
        case IntDist(ops*) => ops.map(_.vars).foldLeft(Set())(_ ++ _)
        case IntEq(op1, op2) => op1.vars ++ op2.vars
        case BoolEq(op1, op2) => op1.vars ++ op2.vars
        case LE(op1, op2) => op1.vars ++ op2.vars
        case GE(op1, op2) => op1.vars ++ op2.vars
        case LT(op1, op2) => op1.vars ++ op2.vars
        case GT(op1, op2) => op1.vars ++ op2.vars
        case _ => throw IllegalStateException("Non exhaustive match")
      } 

    protected def apply(z: Z3Context): Z3AST =
      this match{
        case Add(ops*) => z.mkAdd(ops.map(_(z)): _*)
        case Sub(op1, op2) => z.mkSub(op1(z), op2(z))
        case Mul(ops*) => z.mkMul(ops.map(_(z)): _*)
        case IntNum(c) => z.mkInt(c, z.mkIntSort())
        case IntVar(id) => z.mkIntConst(id)
        case And(ops*) => if (ops.isEmpty) BoolNum(true)(z) else z.mkAnd(ops.map(_(z)): _*)
        case Or(ops*) => z.mkOr(ops.map(_(z)): _*)
        case Xor(op1, op2) => z.mkXor(op1(z), op2(z))
        case Iff(op1, op2) => z.mkIff(op1(z), op2(z))
        case Not(op) => z.mkNot(op(z))
        case BoolDist(op1, op2) => z.mkDistinct(op1(z), op2(z))
        case IntDist(ops*) => z.mkDistinct(ops.map(_(z)): _*)
        case IntEq(op1, op2) => z.mkEq(op1(z), op2(z))
        case BoolEq(op1, op2) => z.mkEq(op1(z), op2(z))
        case LE(op1, op2) => z.mkLE(op1(z), op2(z))
        case GE(op1, op2) => z.mkGE(op1(z), op2(z))
        case LT(op1, op2) => z.mkLT(op1(z), op2(z))
        case GT(op1, op2) => z.mkGT(op1(z), op2(z))
        case BoolNum(c) => if c then z.mkTrue() else z.mkFalse()
        case BoolVar(id) => z.mkBoolConst(id)
        case _ => throw IllegalStateException("Non exhaustive match")
      }
    
    def solve: (Option[NumQuery], () => Unit) =
      val z: Z3Context = Z3Context("MODEL" -> true)
      val solv:Z3Solver = z.mkSolver()
      solv.assertCnstr(this(z))
      val res: Option[NumQuery] = solv.check() match 
        case None => throw IllegalStateException("Z3 Failed")
        case Some(false) => None
        case Some(true) => 
          val mod = solv.getModel()
          Some(NumQuery(vars.map((v: Var) => v match {
            case IntVar(id) => (id, IntNum(mod.getConstInterpretation(id).getOrElse(throw IllegalStateException("The variable should be defined")).toString.toInt))
            case BoolVar(id) => (id, BoolNum(mod.getConstInterpretation(id).getOrElse(throw IllegalStateException("The variable should be defined")).toString.toBoolean))
          }).toMap))
      
      (res, () => z.delete())


  }

  trait Const extends Constr
  trait Var extends Constr
  
  trait IntConstr extends Constr{
    def +(b: IntConstr): IntConstr = Add(this, b)
    def -(b: IntConstr): IntConstr = Sub(this, b)
    def *(b: IntConstr): IntConstr = Mul(this, b)
    def ===(b: IntConstr): BoolConstr = IntEq(this, b)
    def !==(b: IntConstr): BoolConstr = IntDist(this, b)
    def <=(b: IntConstr): BoolConstr = LE(this, b)
    def >=(b: IntConstr): BoolConstr = GE(this, b)
    def >(b: IntConstr): BoolConstr = GT(this, b)
    def <(b: IntConstr): BoolConstr = LT(this, b)
  }
  case class Add(ops: IntConstr*) extends IntConstr
  case class Sub(op1: IntConstr, op2: IntConstr) extends IntConstr
  case class Mul(ops: IntConstr*) extends IntConstr

  case class IntNum(c: Int) extends IntConstr with Const
  case class IntVar(id: String) extends IntConstr with Var
  trait BoolConstr extends Constr{
    def ===(b: BoolConstr): BoolConstr = BoolEq(this, b)
    def !==(b: BoolConstr): BoolConstr = BoolDist(this, b)
    def &&(b: BoolConstr): BoolConstr = And(this, b)
    def ||(b: BoolConstr): BoolConstr = Or(this, b)
    def ^(b: BoolConstr): BoolConstr = Xor(this, b)
    def <=>(b: BoolConstr): BoolConstr = Iff(this, b)
    def unary_! : BoolConstr = Not(this)
  }
  case class And(ops: BoolConstr*) extends BoolConstr
  case class Or(ops: BoolConstr*) extends BoolConstr
  case class Xor(op1: BoolConstr, op2: BoolConstr) extends BoolConstr
  case class Iff(op1: BoolConstr, op2: BoolConstr) extends BoolConstr
  case class Not(op: BoolConstr) extends BoolConstr
  case class BoolDist(op1: BoolConstr, op2: BoolConstr) extends BoolConstr
  case class IntDist(ops: IntConstr*) extends BoolConstr
  case class BoolEq(op1: BoolConstr, op2: BoolConstr) extends BoolConstr
  case class IntEq(op1: IntConstr, op2: IntConstr) extends BoolConstr
  case class LE(op1: IntConstr, op2: IntConstr) extends BoolConstr
  case class GE(op1: IntConstr, op2: IntConstr) extends BoolConstr
  case class LT(op1: IntConstr, op2: IntConstr) extends BoolConstr
  case class GT(op1: IntConstr, op2: IntConstr) extends BoolConstr
  case class BoolNum(c: Boolean) extends BoolConstr with Const
  case class BoolVar(id: String) extends BoolConstr with Var

  given Conversion[Int, IntNum] with
    def apply(id: Int) = IntNum(id)

  given Conversion[Seq[Int], Seq[IntNum]] with
    def apply(id: Seq[Int]) = id.map(IntNum(_))

  given Conversion[Boolean, BoolNum] with
    def apply(id: Boolean) = BoolNum(id)

  def IntVar(c: Seq[String]): Seq[IntVar] = c.map(IntVar(_))
  def IntVar(c: Int): IntVar = IntVar(c.toString)
  @targetName("IntVarSeqInt")
  def IntVar(c: Seq[Int]): Seq[IntVar] = c.map(IntVar(_))
  def IntVar(c: (Int, Int)): IntVar = IntVar(s"${c._1},${c._2}")
  @targetName("IntVarSeqIntPair")
  def IntVar(c: Seq[(Int, Int)]): Seq[IntVar] = c.map(IntVar(_))

  def BoolVar(c: Seq[String]): Seq[BoolVar] = c.map(BoolVar(_))
  def And(ops: Seq[BoolConstr]): And = And(ops: _*)
  def Or(ops: Seq[BoolConstr]): Or = Or(ops: _*)
  def Add(ops: Seq[IntConstr]): Add = Add(ops: _*)
  def Mul(ops: Seq[IntConstr]): Mul = Mul(ops: _*)
  def IntDist(ops: Seq[IntConstr]): IntDist = IntDist(ops: _*)

}