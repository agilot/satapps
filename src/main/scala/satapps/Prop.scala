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

  def toCNF: Expr = 

    def renameVars(e: Expr): Expr =
      e match{
        case Variable(s) => Variable("u" + s)
        case Not(v) => Not(renameVars(v))
        case And(l, r) => And(renameVars(l), renameVars(r))
        case Or(l, r) => Or(renameVars(l), renameVars(r))
        case Xor(l, r) => Xor(renameVars(l), renameVars(r))
      }
    

    def tseytin(e: Expr, pref: String): (String, Map[Variable, Expr]) =

      e match{
        case Variable(v) => (v, Map())
        case And(l, r) =>
          val tl = tseytin(l, pref + "0")
          val tr = tseytin(r, pref + "1")
          val m = tl._2 ++ tr._2 
          (pref, m + (Variable(pref) -> And(Variable(tl._1), Variable(tr._1))))
        case Or(l, r) =>
          val tl = tseytin(l, pref + "0")
          val tr = tseytin(r, pref + "1")
          val m = tl._2 ++ tr._2 
          (pref, m + (Variable(pref) -> Or(Variable(tl._1), Variable(tr._1))))
        case Xor(l, r) =>
          val tl = tseytin(l, pref + "0")
          val tr = tseytin(r, pref + "1")
          val m = tl._2 ++ tr._2 
          (pref, m + (Variable(pref) -> Xor(Variable(tl._1), Variable(tr._1))))
        case Not(exp) =>
          val te = tseytin(exp, pref + "0")
          (pref, te._2 + (Variable(pref) -> Not(Variable(te._1))))
      }
    
    def clauseConv(ve: (Variable, Expr)) =
      ve._2 match{
        case Not(v) => And(Or(Not(v), Not(ve._1)), Or(v, ve._1))
        case And(v1, v2) => And(And(Or(Not(v1), Or(Not(v2), ve._1)), Or(v1, Not(ve._1))), Or(v2, Not(ve._1)))
        case Or(v1, v2) => And(And(Or(v1, Or(v2, Not(ve._1))), Or(Not(v1), ve._1)), Or(Not(v2), ve._1))
        case Xor(v1, v2) => And(And(Or(Not(v1), Or(Not(v2), Not(ve._1))), Or(v1, Or(v2, Not(ve._1)))), And(Or(v1, Or(Not(v2), ve._1)), Or(Not(v1), Or(v2, ve._1))))
        case _ => throw IllegalArgumentException("This case should never occur")
      }

    val ts = tseytin(renameVars(this), "r")
    And(Variable(ts._1), Prop.andAll(ts._2.toList.map(clauseConv)))
  
}

case class Variable(id: String) extends Expr
case class Not(exp: Expr) extends Expr
case class And(left: Expr, right: Expr) extends Expr
case class Or(left: Expr, right: Expr) extends Expr
case class Xor(left: Expr, right: Expr) extends Expr{
  def to2CNF() = And(Or(left, right), Or(Not(left), Not(right)))
}

given Conversion[String, Expr] with
  def apply(id: String) = Variable(id)

object Prop{

  def xnorTo2CNF(e: Not): Expr = 
    e.exp match {
      case Xor(l, r) => And(Or(Not(l), r), Or(l, Not(r)))
      case _ => throw IllegalArgumentException("Not(Xor(l, r)) required")
    }
  
  def xor2ClauseToCNF(e: Expr):Expr = 
    e match{
      case x : Xor => x.to2CNF()
      case Not(Xor(_, _)) => xnorTo2CNF(e.asInstanceOf[Not])
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