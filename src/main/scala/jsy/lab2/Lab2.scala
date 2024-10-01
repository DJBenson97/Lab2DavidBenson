package jsy.lab2

object Lab2 extends jsy.util.JsyApplication {
  import ast._
  
  /*
   *
   * CSCI 3155: Lab 2
   * David Benson
   *
   * Partner: None
   * Collaborators: None
   * 
   */

  def toNumber(v: Expr): Double = {
    require(isValue(v))
    (v: @unchecked) match {
      case N(n) => n
      case B(b) => if (b) 1.0 else 0.0
      case S(s) => try s.toDouble catch { case _: NumberFormatException => Double.NaN }
      case Undefined => Double.NaN
      case _ => throw new UnsupportedOperationException(s"Cannot convert $v to a number")
    }
  }

  def toBoolean(v: Expr): Boolean = {
    require(isValue(v))
    (v: @unchecked) match {
      case B(b) => b
      case N(n) => n != 0.0 && !n.isNaN
      case S(s) => s.nonEmpty
      case Undefined => false
      case _ => throw new UnsupportedOperationException(s"Cannot convert $v to a boolean")
    }
  }

  def toStr(v: Expr): String = {
    require(isValue(v))
    (v: @unchecked) match {
      case S(s) => s
      case N(n) => if (n.isWhole) n.toInt.toString else n.toString
      case B(b) => b.toString
      case Undefined => "undefined"
      case _ => throw new UnsupportedOperationException(s"Cannot convert $v to a string")
    }
  }

  type Env = Map[String, Expr]
  val empty: Env = Map()
  
  def lookup(env: Env, x: String): Expr = env(x)
  
  def extend(env: Env, x: String, v: Expr): Env = {
    require(isValue(v))
    env + (x -> v)
  }

def eval(env: Env, e: Expr): Expr = {
  e match {
    /* Base Cases */
    case N(_) | B(_) | S(_) | Undefined => e
    case Var(x) => lookup(env, x)

    /* Inductive Cases */
    case Unary(Neg, e1) => N(-toNumber(eval(env, e1)))
    case Unary(Not, e1) => B(!toBoolean(eval(env, e1)))

    case Binary(Plus, e1, e2) =>
      (eval(env, e1), eval(env, e2)) match {
        case (S(s1), v2) => S(s1 + toStr(v2))
        case (v1, S(s2)) => S(toStr(v1) + s2)
        case (N(n1), N(n2)) => N(n1 + n2)
        case (B(b), N(n)) => N((if (b) 1 else 0) + n)
        case (N(n), B(b)) => N(n + (if (b) 1 else 0))
        case (Undefined, _) => N(Double.NaN)
        case (_, Undefined) => N(Double.NaN)
        case _ => throw new UnsupportedOperationException("Invalid operand types for +")
      }

    case Binary(Minus, e1, e2) => N(toNumber(eval(env, e1)) - toNumber(eval(env, e2)))
    case Binary(Times, e1, e2) => N(toNumber(eval(env, e1)) * toNumber(eval(env, e2)))
    case Binary(Div, e1, e2) => N(toNumber(eval(env, e1)) / toNumber(eval(env, e2)))

    case Binary(Gt, e1, e2) =>
      (eval(env, e1), eval(env, e2)) match {
        case (N(n1), N(n2)) => B(n1 > n2)
        case _ => throw new UnsupportedOperationException("Invalid operand types for >")
      }

    case Binary(Lt, e1, e2) =>
      (eval(env, e1), eval(env, e2)) match {
        case (N(n1), N(n2)) => B(n1 < n2)
        case _ => throw new UnsupportedOperationException("Invalid operand types for <")
      }

    case Binary(Le, e1, e2) =>
      (eval(env, e1), eval(env, e2)) match {
        case (N(n1), N(n2)) => B(n1 <= n2)
        case _ => B(false)
      }

    case Binary(Ge, e1, e2) =>
      (eval(env, e1), eval(env, e2)) match {
        case (N(n1), N(n2)) => B(n1 >= n2)
        case _ => B(false)
      }

    case Binary(Eq, e1, e2) =>
      (eval(env, e1), eval(env, e2)) match {
        case (N(n1), N(n2)) => B(n1 == n2)
        case (Undefined, _) => B(false)
        case (_, Undefined) => B(false)
        case _ => B(false)
      }

    case Binary(Ne, e1, e2) =>
      (eval(env, e1), eval(env, e2)) match {
        case (N(n1), N(n2)) => B(n1 != n2)
        case (Undefined, _) => B(true)
        case (_, Undefined) => B(true)
        case _ => B(true)
      }

    case Binary(And, e1, e2) =>
      (eval(env, e1), eval(env, e2)) match {
        case (B(b1), B(b2)) => B(b1 && b2)
        case (N(0), _) => N(0)
        case (_, N(0)) => N(0)
        case _ => throw new UnsupportedOperationException("Invalid operand types for &&")
      }

    case Binary(Or, e1, e2) =>
      (eval(env, e1), eval(env, e2)) match {
        case (B(b1), B(b2)) => B(b1 || b2)
        case (B(true), _) => B(true)
        case (_, B(true)) => B(true)
        case (N(n), B(false)) => N(n)
        case (B(false), N(n)) => N(n)
        case _ => B(false)
      }

    case Binary(Seq, e1, e2) => 
      eval(env, e1); eval(env, e2)

    case If(e1, e2, e3) =>
      if (toBoolean(eval(env, e1))) eval(env, e2) else eval(env, e3)

    case ConstDecl(x, e1, e2) =>
      val v1 = eval(env, e1)
      eval(extend(env, x, v1), e2)

    case Print(e1) =>
      println(pretty(eval(env, e1)))
      Undefined

    case _ => throw new UnsupportedOperationException("Unknown expression type")
  }
}

  /* Interface to run your interpreter starting from an empty environment. */
  def eval(e: Expr): Expr = {
    require(closed(e))
    eval(empty, e)
  }

  /* Interface to run your interpreter from a string. */
  def eval(s: String): Expr = eval(Parser.parse(s))

  /* Interface to run your interpreter on an input file. */
  def processFile(file: java.io.File): Unit = {
    if (debug) { println("Parsing ...") }

    val expr = Parser.parseFile(file)

    if (debug) {
      println("\nExpression AST:\n  " + expr)
      println("------------------------------------------------------------")
    }

    if (debug) { println("Evaluating ...") }

    val v = eval(expr)

    println(pretty(v))
  }
}