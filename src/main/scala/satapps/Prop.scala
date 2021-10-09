package satapps

abstract class Expr {
      
  def varSet(): Set[Variable] =
    this match{
      case v: Variable => Set(v)
      case Not(v) => v.varSet()
      case And(l, r) => l.varSet() ++ r.varSet()
      case Or(l, r) => l.varSet() ++ r.varSet()
      case Xor(l, r) => l.varSet() ++ r.varSet()
      case _ => Set()
    }
  
  override def toString() =
    this match{
      case Variable(s) => s
      case Not(v) => s"~${v}"
      case And(l, r) => s"(${l} ^ ${r})"
      case Or(l, r) => s"(${l} v ${r})"
      case Xor(l, r) => s"(${l} xor ${r})"
      case T => "T"
      case F => "F"
    }

  def eval(e: Map[Variable, Expr], lazyEv: Side = Left): Expr =
    this match{
      case T => T
      case F => F
      case v: Variable => if (e.contains(v)) e(v) else v
      case Not(v) => 
        val ve = v.eval(e, lazyEv)
        ve match{
          case T => F
          case F => T
          case _ => Not(ve)
        }
      case And(l, r) =>
        lazy val ev1 = 
          lazyEv match{
            case Left => l.eval(e, lazyEv)
            case Right => r.eval(e, lazyEv)
          }
        
        
        lazy val ev2 = 
          lazyEv match{
            case Left => r.eval(e, lazyEv)
            case Right => l.eval(e, lazyEv)
          }
         
        if (ev1 == F || ev2 == F) F
        else if (ev1 == T) ev2
        else if (ev2 ==  T) ev1
        else And(ev1, ev2)

      case Or(l, r) => 
        lazy val ev1 = 
          lazyEv match{
            case Left => l.eval(e, lazyEv)
            case Right => r.eval(e, lazyEv)
          }
        lazy val ev2 = 
          lazyEv match{
            case Left => r.eval(e, lazyEv)
            case Right => l.eval(e, lazyEv)
          }
         
        if (ev1 == T || ev2 == T) T
        else if (ev1 == F) ev2
        else if (ev2 == F) ev1
        else Or(ev1, ev2)
      
      case x: Xor => 
        x.to2CNF().eval(e, lazyEv)
    }


  def &(e2: Expr) = And(this, e2)
  def |(e2: Expr) = Or(this, e2)
  def &&(e2: Expr) = And(this, e2)
  def ||(e2: Expr) = Or(this, e2)
  def unary_! = Not(this)
  def unary_~ = Not(this)
  
  def isCNFClause: Boolean =
    this match {
      case Or(l, r) => l.isCNFClause && r.isCNFClause
      case Variable(_) => true
      case Not(Variable(_)) => true
      case _ => false
    }
  
  def isCNF: Boolean =    
    this match {
      case And(l, r) => l.isCNF && r.isCNF
      case _ => isCNFClause
    }

  def toCNF: Expr = 
    val expEv = eval(Map())

    def renameVars(e: Expr): Expr =
      e match{
        case Variable(s) => Variable("u" + s)
        case Not(v) => Not(renameVars(v))
        case And(l, r) => And(renameVars(l), renameVars(r))
        case Or(l, r) => Or(renameVars(l), renameVars(r))
        case Xor(l, r) => Xor(renameVars(l), renameVars(r))
        case _ => throw IllegalArgumentException("This state should never occur")
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
        case _ => throw IllegalArgumentException("This state should never occur")
      }
    
    def clauseConv(ve: (Variable, Expr)) =
      ve._2 match{
        case Not(v) => And(Or(Not(v), Not(ve._1)), Or(v, ve._1))
        case And(v1, v2) => And(And(Or(Not(v1), Or(Not(v2), ve._1)), Or(v1, Not(ve._1))), Or(v2, Not(ve._1)))
        case Or(v1, v2) => And(And(Or(v1, Or(v2, Not(ve._1))), Or(Not(v1), ve._1)), Or(Not(v2), ve._1))
        case Xor(v1, v2) => And(And(Or(Not(v1), Or(Not(v2), Not(ve._1))), Or(v1, Or(v2, Not(ve._1)))), And(Or(v1, Or(Not(v2), ve._1)), Or(Not(v1), Or(v2, ve._1))))
        case _ => throw IllegalArgumentException("This case should never occur")
      }

    val ts = tseytin(renameVars(expEv), "r")
    And(Variable(ts._1), Prop.andAll(ts._2.toList.map(clauseConv)))
  
}

case class Variable(id: String) extends Expr
case class Not(exp: Expr) extends Expr
case class And(left: Expr, right: Expr) extends Expr
case class Or(left: Expr, right: Expr) extends Expr
case class Xor(left: Expr, right: Expr) extends Expr{
  def to2CNF() = And(Or(left, right), Or(Not(left), Not(right)))
}
case object T extends Expr
case object F extends Expr

abstract class Side
case object Right extends Side
case object Left extends Side

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