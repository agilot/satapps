package satapps

abstract class Expr {
      
  def varSet(): Set[Variable] =
    this match{
      case v: Variable => Set(v)
      case Not(v) => v.varSet()
      case And(l, r) => l.varSet() ++ r.varSet()
      case Or(l, r) => l.varSet() ++ r.varSet()
      case Xor(l, r) => l.varSet() ++ r.varSet()
    }
  
  override def toString() =
    this match{
      case Variable(s) => s
      case Not(v) => s"~${v}"
      case And(l, r) => s"(${l} ^ ${r})"
      case Or(l, r) => s"(${l} v ${r})"
      case Xor(l, r) => s"(${l} xor ${r})"
    }

  def eval(e: Map[Variable, Boolean]): Boolean =
    this match{
      case v: Variable => e(v)
      case Not(v) => !v.eval(e)
      case And(l, r) => l.eval(e) && r.eval(e)
      case Or(l, r) => l.eval(e) || r.eval(e)
      case Xor(l, r) => l.eval(e) ^ r.eval(e)
    }

  def &(e2: Expr) = And(this, e2)
  def |(e2: Expr) = Or(this, e2)
  def &&(e2: Expr) = And(this, e2)
  def ||(e2: Expr) = Or(this, e2)
  def unary_! = Not(this)
  def unary_~ = Not(this)

  def toSAT(): Expr = ???

}

case class Variable(id: String) extends Expr
case class Not(exp: Expr) extends Expr
case class And(left: Expr, right: Expr) extends Expr
case class Or(left: Expr, right: Expr) extends Expr
case class Xor(left: Expr, right: Expr) extends Expr{
  def toCNF() = And(Or(left, right), Or(Not(left), Not(right)))
}


object Prop{
    

  def xnorToCNF(e: Not): Expr = 
    e.exp match {
      case Xor(l, r) => And(Or(Not(l), r), Or(l, Not(r)))
      case _ => throw IllegalArgumentException("Not(Xor(l, r)) required")
    }
  
  def xor2ClauseToCNF(e: Expr):Expr = 
    e match{
      case x : Xor => x.toCNF()
      case Not(Xor(_, _)) => xnorToCNF(e.asInstanceOf[Not])
      case And(l, r) => And(xor2ClauseToCNF(l), xor2ClauseToCNF(r))
      case _ => throw IllegalArgumentException("Not a xor 2-clause")
    }
  
  def andAll(ex : List[Expr]) = ex.reduce(And(_, _))
  def orAll(ex: List[Expr]) = ex.reduce(Or(_, _))

  def all(v: List[Variable]): Expr = andAll(v)
  def none(v: List[Variable]): Expr = andAll(v.map(Not(_)))
  def same(v : List[Variable]): Expr = Or(all(v), none(v))
  def atLeastOne(v: List[Variable]): Expr = orAll(v)
  def exactlyOne(v: List[Variable]): Expr = 
    def notPairs(l: List[Variable]): Expr =
      l match
        case List(x, y) => Not(And(x, y))
        case x :: xs => 
          And(andAll(xs.map(y => Not(And(x, y)))), notPairs(xs))
        case _ => throw IllegalArgumentException("This state should never occur")
    v match{
      case Nil => throw IllegalArgumentException("No Variable")
      case List(x) => x
      case _ => And(atLeastOne(v),notPairs(v))
    }
}