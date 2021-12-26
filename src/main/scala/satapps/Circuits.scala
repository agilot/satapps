package satapps

abstract class Circuit {
  def apply(assign: Map[String, Boolean]): Boolean =
    this match{
      case Input(v) => assign(v)
      case AndGate(i1, i2) => i1(assign) && i2(assign)
      case OrGate(i1, i2) => i1(assign) || i2(assign)
      case NotGate(i) => !i(assign)
      case Constant(c) => c
    }

  def toExpr: Expr = 
    this match{
      case Input(v) => Variable(v)
      case AndGate(i1, i2) => And(i1.toExpr, i2.toExpr)
      case OrGate(i1, i2) => Or(i1.toExpr, i2.toExpr)
      case NotGate(i) => Not(i.toExpr)
      case Constant(c) => if(c) T else F 
    }

  override def toString: String =
    this match{
      case Input(v) => v
      case Constant(c) => if(c) "1" else "0"
      case AndGate(i1, i2) => "(" + i1.toString + "^" + i2.toString + ")"
      case OrGate(i1, i2) => "(" + i1.toString + "v" + i2.toString + ")"
      case NotGate(i) => "!" + i.toString
    }
  
}
case class AndGate(in1: Circuit, in2: Circuit) extends Circuit
case class OrGate(in1: Circuit, in2: Circuit) extends Circuit
case class NotGate(in: Circuit) extends Circuit
case class Input(v: String) extends Circuit
case class Constant(c: Boolean) extends Circuit

object Circuits{

  def xorGate(in1: Circuit, in2: Circuit): Circuit = OrGate(AndGate(in1, NotGate(in2)), AndGate(NotGate(in1), in2))
  def iffGate(in1: Circuit, in2: Circuit): Circuit = OrGate(AndGate(in1, in2), AndGate(NotGate(in1), NotGate(in2)))
  def binAdder(x: Circuit, y: Circuit, cin: Circuit) = 
    (xorGate(x, xorGate(y, cin)), OrGate(AndGate(x, y), OrGate(AndGate(x, cin), AndGate(y, cin))))
  def intAdder(x: List[Circuit], y: List[Circuit]): List[Circuit] =
    val z = x.zip(y)
    def rec(xs: List[(Circuit, Circuit)]): (List[Circuit], Circuit) =
      xs match{
        case Nil => (Nil, Constant(false))
        case h :: t => 
          val add = rec(t)
          val bin = binAdder(h._1, h._2, add._2)
          (bin._1 :: add._1, bin._2)
      }
    rec(z)._1
  
  def bitwiseAnd(x: List[Circuit], y: List[Circuit]): List[Circuit] = x.zip(y).map(AndGate.apply)
  def bitwiseOr(x: List[Circuit], y: List[Circuit]): List[Circuit] = x.zip(y).map(OrGate.apply)
  def bitwiseNot(x: List[Circuit]): List[Circuit] = x.map(NotGate.apply)
  def bitwiseEq(x: List[Circuit], y: List[Circuit]): List[Circuit] = x.zip(y).map(iffGate)

  def toBinary(i: Int, d: Int): List[Circuit] = 
    String.format(s"%0${d}d", i.toBinaryString.toInt).toList.map(c => Constant(if(c.toInt - 48 == 0) false else true))

  def subsetSum(l: List[Int], k: Int, solv: SATSolver): Boolean =
    val max = l.reduce(_ + _).toBinaryString.length
    val lb: List[List[Circuit]] = l.map(toBinary(_, max))
    print(lb)
    val lbWSubs: List[List[Circuit]] = lb.zipWithIndex.map((e, idx) => bitwiseAnd(e, List.fill(max)(Input(s"s${idx}"))))
    val sol = CNFSAT.solveSAT(bitwiseEq(lbWSubs.reduceLeft(intAdder), toBinary(k, max)).reduce(AndGate.apply).toExpr.toCNF(), solv)
    println(sol._1.view.filterKeys(_.id.charAt(0) == 'u').toMap)
    sol._2 == SAT
}