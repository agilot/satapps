package satapps

import Z3.*
import z3.scala.*

object Extensions{
  extension (a: Z3Type)
    def +(b: Z3Type): Z3Type = z => z.mkAdd(a(z), b(z))
    def *(b: Z3Type): Z3Type = z => z.mkMul(a(z), b(z))
    def ===(b: Z3Type): Z3Type = z => z.mkEq(a(z), b(z))
    def !==(b: Z3Type): Z3Type = z => z.mkDistinct(a(z), b(z))
    def <=(b: Z3Type): Z3Type = z => z.mkLE(a(z), b(z))
    def >=(b: Z3Type): Z3Type = z => z.mkGE(a(z), b(z))
    def <(b: Z3Type): Z3Type = z => z.mkLT(a(z), b(z))
    def >(b: Z3Type): Z3Type = z => z.mkGT(a(z), b(z))
    def &&(b: Z3Type): Z3Type = z => z.mkAnd(a(z), b(z))
    def ||(b: Z3Type): Z3Type = z => z.mkOr(a(z), b(z))
    def ^(b: Z3Type): Z3Type = z => z.mkXor(a(z), b(z))
    def <=>(b: Z3Type): Z3Type = z => z.mkIff(a(z), b(z))
    def unary_! : Z3Type = (z: Z3Context) => z.mkNot(a(z))

  extension (a: Seq[Z3Type])
    def +(b: Seq[Z3Type]): Z3Type = andAll(a.zip(b).map(_ + _))
    def ===(b: Z3Type): Z3Type = andAll(a.map(_ === b))
    def <=(b: Z3Type): Z3Type = andAll(a.map(_ <= b))
    def >=(b: Z3Type): Z3Type = andAll(a.map(_ >= b))
    def <(b: Z3Type): Z3Type = andAll(a.map(_ < b))
    def >(b: Z3Type): Z3Type = andAll(a.map(_ > b))

  extension (a: Z3Type)
    def toStringed(): String = 
      val z: Z3Context = Z3Context()
      val res = a(z).toString
      z.delete()
      res

  extension (a: Matrix[Boolean])
    def ^(m2: Matrix[Boolean]): Matrix[Boolean] = Matrix[Boolean](a.unravel.zip(m2.iterator.toList).map(_^_), a.r, a.c)
    def ||(m2: Matrix[Boolean]): Matrix[Boolean] = Matrix[Boolean](a.unravel.zip(m2.iterator.toList).map(_||_), a.r, a.c)
    def complement : Matrix[Boolean] = Matrix[Boolean](a.unravel.map(!_), a.r, a.c)
    
    def *(b2: Matrix[Boolean]): Matrix[Boolean] =
      require(a.c == b2.r)
      Matrix[Boolean](
        (for(i <- 0 until a.r; j <- 0 until b2.c)
          yield (for(k <- 0 until a.c) yield a(i, k) && b2(k, j)).reduce(_ || _)).toList
        , a.r, b2.c)

    def pow(n: Int): Matrix[Boolean] =
      require(n > 0 && a.r == a.c)
      n match{
        case 1 => a
        case _ => *(pow(n - 1))
      }

    def transClos(): Matrix[Boolean] = 
      require(a.r == a.c)
      def transPow(bef: Matrix[Boolean], aft: Matrix[Boolean]): Matrix[Boolean] =
        if(bef equals aft)
          bef
        else 
          transPow(aft, aft || (a * aft))
      
      transPow(a, a || (a * a))

    def toString(): String = (for(i <- 0 until a.r) yield (for(j <- 0 until a.c) yield (if (a(i, j)) "1" else "0") ++ " ").reduce(_ ++ _) ++ "\n").reduce(_ ++ _)
}