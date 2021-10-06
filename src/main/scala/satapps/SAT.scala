package satapps


abstract class SATResult
case object SAT extends SATResult
case object UNSAT extends SATResult
case object UNKNOWN extends SATResult

abstract class SATSolver
case object BruteForce extends SATSolver

object CNFSAT{

  def isSAT(e: Expr): Boolean =    
    def isClause(ex: Expr): Boolean =
      ex match {
        case And(l, r) => isClause(l) && isClause(r)
        case Variable(_) => true
        case Not(Variable(_)) => true
        case _ => false
      }
    
    e match {
      case Or(l, r) => isSAT(l) && isSAT(r)
      case _ => isClause(e)
    }

  def solveSAT(e: Expr, solv: SATSolver): (Map[Variable, Boolean], SATResult) =
    solv match{
      case BruteForce => 
        val l = e.varSet().toList
        def solve(unused: List[Variable], env: Map[Variable, Boolean]): (Map[Variable, Boolean], Boolean) =
          unused match{
            case Nil => 
              if (e.eval(env)) (env, true) else (env, false)
            case x :: xs => 
              val (e1, b1) = solve(xs, env + (x -> false))
              if(b1) (e1, true) else
                val (e2, b2) = solve(xs, env + (x -> true))
                if(b2) (e2, true) else
                  (env, false)
          }
        val (env, res) = solve(l, Map())
        if(res) (env, SAT) else (env, UNSAT)
    }
    
  def removeAux(m: Map[Variable, Boolean]): Map[Variable, Boolean] =
    m.filterKeys(_.id.head == 'u').toList.map((f, v) => (Variable(f.id.tail) -> v)).toMap
}

object TwoSAT{

  def is2SAT(e: Expr): Boolean =

    def is2Clause(e: Or): Boolean = 
      (e.left, e.right) match {
        case (Variable(_), Variable(_)) => true
        case (Not(Variable(_)), Not(Variable(_))) => true
        case (Variable(_), Not(Variable(_))) => true
        case (Not(Variable(_)), Variable(_)) => true
        case _ => false
      }
    
    e match {
      case Not(Variable(_)) => true
      case Variable(_) => true
      case Or(l, r) => is2Clause(Or(l, r))
      case And(l, r) => is2SAT(l) && is2SAT(r)
      case _ => false
    }

  def solve2SAT(e: Expr): SATResult =

    val s = e.varSet()

    def gen2SATMap(): Map[Variable, Vertex] = 
      s.zip(Range(0, s.size * 2, 2)).toMap
    
    val m = gen2SATMap()

    def gen2SATGraph(e: Expr) = 
      
      def gen2SATEdgeSet(ex: Expr): Set[Edge] =
        ex match{
          case And(l, r) => gen2SATEdgeSet(l) ++ gen2SATEdgeSet(r)
          case Or(l, r) => 
          (l, r) match
            case (Variable(a), Variable(b)) => Set((m(Variable(a)) + 1, m(Variable(b)))) ++ Set((m(Variable(b)) + 1, m(Variable(a))))
            case (Not(Variable(a)), Variable(b)) => Set((m(Variable(a)), m(Variable(b)))) ++ Set((m(Variable(b)) + 1, m(Variable(b)) + 1))
            case (Variable(a), Not(Variable(b))) => Set((m(Variable(a)) + 1 , m(Variable(b)) + 1)) ++ Set((m(Variable(b)) , m(Variable(b))))
            case (Not(Variable(a)), Not(Variable(b))) => Set((m(Variable(a)), m(Variable(b)) + 1)) ++ Set((m(Variable(b)), m(Variable(a)) + 1))
            case _ => throw IllegalArgumentException("Not an instance of 2SAT")
          case _ => throw IllegalArgumentException("Not an instance of 2SAT")
        }
      
      GraphFromEdgeSet((0 until s.size * 2).toSet, gen2SATEdgeSet(e)).transClos()
    
    val g = gen2SATGraph(e)

    def checkGraph() = !(for(p <- m) yield g.adjMat(p._2, p._2 + 1) || g.adjMat(p._2 + 1, p._2)).reduce(_ || _)
    
    if (checkGraph()) SAT else UNSAT
}

