package satapps


abstract class SATResult
case object SAT extends SATResult
case object UNSAT extends SATResult
case object UNKNOWN extends SATResult

abstract class SATSolver
case object BruteForce extends SATSolver
case object DPLL extends SATSolver

object CNFSAT{

  type Env = Map[Variable, Expr]

  def units(e: Expr): Env =
    e match{
      case T => Map()
      case F => Map()
      case Or(l, r) => Map()
      case And(l, r) => units(l) ++ units(r)
      case Not(Variable(s)) => Map(Variable(s) -> F)
      case Variable(s) => Map(Variable(s) -> T)
      case _ => throw IllegalArgumentException("Not in CNF Form")
    }

  def pures(e: Expr): Env =
    val set = e.varSet()
    val m = set.map((_ -> (0, 0))).toMap
    def count(ex : Expr): Map[Variable, (Int, Int)] =
      ex match{
        case T => m
        case F => m
        case And(l, r) => 
          val ml = count(l)
          val mr = count(r)
          ml.map((k, v) => k -> (v._1 + mr(k)._1, v._2 + mr(k)._2))
        case Or(l, r) =>
          val ml = count(l)
          val mr = count(r)
          ml.map((k, v) => k -> (v._1 + mr(k)._1, v._2 + mr(k)._2))
        case Not(Variable(s)) =>
          m.updated(Variable(s), (0, 1))
        case Variable(s) =>
          m.updated(Variable(s), (1, 0))
        case _ => throw IllegalArgumentException("This case should never occur")
      }

    count(e).filter((k, v) => v._1 == 0 || v._2 == 0).map((k, v) => if(v._2 == 0) k -> T else k -> F)
    
  def removePures(e: Expr): (Expr, Env) = 
    val p = pures(e)
    val ev = e.eval(p)
    if(ev == e) (ev, p) else 
      val rec = removePures(ev)
      (rec._1, p ++ rec._2)

  def removeUnits(e: Expr): (Expr, Env) = 
    val u = units(e)
    val ev = e.eval(u)
    if(ev == e) (ev, u) else 
      val rec = removeUnits(ev)
      (rec._1, u ++ rec._2)
    
  def removePuresAndUnits(e: Expr): (Expr, Env) = 
    val u = units(e)
    val ev1 = e.eval(u)
    val p = pures(ev1) ++ u
    val ev2 = ev1.eval(p)
    if(ev2 == e) (ev2, p) else 
      val rec = removePuresAndUnits(ev2)
      (rec._1, p ++ rec._2)
    

  def solveSAT(e: Expr, solv: SATSolver): (Env, SATResult) =
    solv match{
      case DPLL =>
        val l = e.varSet()
        def solve(ex: Expr, unused: Set[Variable], env: Env) : (Env, Boolean) =
          println("yo")
          val ru = removePuresAndUnits(ex)
          val newUnused = unused -- ru._2.keys
          val newEnv = ru._2 ++ env
          //println(s"ex = ${ex}, unused = ${unused}, env = ${env}, ru = ${ru}, newUnused = ${newUnused}, newEnv =${newEnv}")
          ru._1 match{
            case F => (newEnv, false)
            case T => (newEnv, true)
            case _ =>
              val v = newUnused.toList.head
              val newUnused2 = newUnused - v
              val newEnv2 = newEnv + (v -> T)
              val newExp2 = ru._1.eval(newEnv2)
              val s1 = solve(newExp2, newUnused2, newEnv2)
              if (s1._2) s1
              else
                val newEnv3 = newEnv + (v -> F)
                val newExp3 = ru._1.eval(newEnv3)
                val s2 = solve(newExp3, newUnused2, newEnv3)
                s2
          }
        val (env, res) = solve(e, l, Map())
        if(res) (env, SAT) else (env, UNSAT)

      case BruteForce => 
        val l = e.varSet().toList
        def solve(unused: List[Variable], env: Env): (Env, Boolean) =
          unused match{
            case Nil => 
              if (e.eval(env) == T) (env, true) else (env, false)
            case x :: xs => 
              val (e1, b1) = solve(xs, env + (x -> F))
              if(b1) (e1, true) else
                val (e2, b2) = solve(xs, env + (x -> T))
                if(b2) (e2, true) else
                  (env, false)
          }
        val (env, res) = solve(l, Map())
        if(res) (env, SAT) else (env, UNSAT)
    }
    
  def removeAux(m: Env): Env =
    m.view.filterKeys(_.id.head == 'u').toMap.toList.map((f, v) => (Variable(f.id.tail) -> v)).toMap
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

