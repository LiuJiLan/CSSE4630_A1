package tip.analysis

import tip.ast.AstNodeData.DeclarationData
import tip.ast._
import tip.cfg.CfgOps._
import tip.cfg.{CfgNode, CfgStmtNode, ProgramCfg}
import tip.lattices.{MapLattice, BorrowLattice}
import tip.util.MessageHandler

import scala.collection.immutable.Set

/**
  * Borrow Analysis (Part 4).
  *
  * Lattice element for each variable is a pair:
  *   (Status in {STACK, OWNS, DISOWNS, BORROWED, TOP}, Set[AIdentifier])
  * The set means:
  *   - if Status==OWNS: borrowers of this owner
  *   - if Status==BORROWED: possible owners (ŷ)
  *
  * Rules implemented:
  *   Rule 1, 2–6, 7, 8b, 9 and Rule 0 (release on LHS before assign)
  */
class BorrowAnalysis(cfg: ProgramCfg)(implicit declData: DeclarationData)
  extends FlowSensitiveAnalysis(true) {

  val valuelattice = BorrowLattice
  val declaredVars: Set[ADeclaration] = cfg.nodes.flatMap(_.declaredVarsAndParams)
  val statelattice: MapLattice[ADeclaration, BorrowLattice.type] = new MapLattice(valuelattice)
  val lattice: MapLattice[CfgNode, statelattice.type] = new MapLattice(statelattice)
  val domain: Set[CfgNode] = cfg.nodes
  val msgs = new MessageHandler

  import valuelattice._               // Element, BorrowSet, helpers
  import tip.lattices.BorrowElement._ // STACK, OWNS, DISOWNS, BORROWED, TOP

  private def read(id: AIdentifier, env: statelattice.Element): Element = env(declData(id))
  private def write(d: ADeclaration, v: Element, env: statelattice.Element) = env + (d -> v)
  private def statusOfV(v: Element) = valuelattice.statusOf(v)
  private def setOfV(v: Element)    = valuelattice.borrowersOf(v)

  private def msgNone(l: Loc)            = msgs.message(msgs.Reason.None, l)
  private def msgErr(l: Loc, t: String)  = msgs.message(msgs.Reason.OwnershipError, l, t)
  private def msgWarn(l: Loc, t: String) = msgs.message(msgs.Reason.OwnershipWarning, l, t)

  // —— 关键：仅输出纯变量名，避免 AIdentifier.toString 带上 [line:col]
  private def idName(id: AIdentifier): String = id.name

  private val vStack    = make(STACK, Set())
  private val vOwns     = make(OWNS, Set())
  private val vDisowns  = make(DISOWNS, Set())
  private val vBorrowed = make(BORROWED, Set())

  /**
    * Rule 9: evaluate expression and issue errors for invalid * uses.
    * 允许：
    *   *y  当 y::OWNS
    *   **z 当 z::BORROWED
    * 其余 *... 一律报错 "ownership problem: ES"
    */
  def eval(e: AExpr, env: statelattice.Element): Element = e match {
    case id: AIdentifier =>
      read(id, env)

    case _: AAlloc =>
      vOwns

    case AUnaryOp(DerefOp, inner, loc) =>
      inner match {
        // *y
        case y: AIdentifier =>
          statusOfV(read(y, env)) match {
            case Some(OWNS) => msgNone(loc)
            case _          => msgErr(loc, s"ownership problem: *${idName(y)}")
          }
          vStack

        // **z  （inner 是 *z）
        case AUnaryOp(DerefOp, z: AIdentifier, _) =>
          statusOfV(read(z, env)) match {
            case Some(BORROWED) => msgNone(loc)
            case _              => msgErr(loc, s"ownership problem: **${idName(z)}")
          }
          vStack

        // 任何其它 *ES 形式都非法（尽量打印 *标识符）
        case es =>
          es match {
            case ex: AIdentifier => msgErr(loc, s"ownership problem: *${idName(ex)}")
            case _               => msgErr(loc, s"ownership problem: *$es")
          }
          vStack
      }

    // 二元运算：递归检查左右子式是否含非法解引用，结果视为 STACK
    case ABinaryOp(_, left, right, _) =>
      eval(left, env); eval(right, env); vStack

    // 这些都算 STACK
    case _: ANumber | _: AInput | _: ANull =>
      vStack

    // 记录/字段：为稳妥仅递归 record 部分
    case ARecord(fields, _) =>
      fields.foreach(f => eval(f.exp, env)); vStack

    case AFieldAccess(record, _, _) =>
      eval(record, env); vStack

    // 函数调用表达式：本分析为 intraprocedural；仅递归检查参数与目标表达式
    case ACallFuncExpr(target, args, _) =>
      eval(target, env); args.foreach(a => eval(a, env)); vStack

    // 其它表达式（例如 AVarRef &x）在规则里不会出现在一般 E 中；保守处理为 STACK
    case _ =>
      vStack
  }

  def indep(n: CfgNode): Set[CfgNode] = n.pred.toSet
  def join(n: CfgNode, o: lattice.Element) =
    indep(n).map(o(_)).foldLeft(statelattice.bottom)((a, b) => statelattice.lub(a, b))
  def funsub(n: CfgNode, x: lattice.Element) = localTransfer(n, join(n, x))
  def fun(x: lattice.Element) =
    domain.foldLeft(lattice.bottom)((m, a) => m + (a -> localTransfer(a, join(a, x))))

  /**
    * Local transfer:
    *   Rule 1 (vars)
    *   Rule 0 (release on LHS)
    *   Rules 2–6: x = y
    *   Rule 7 & 8b: x = &y  (AST is AVarRef(y, _))
    *   Rule 9: x = E
    */
  def localTransfer(n: CfgNode, s: statelattice.Element): statelattice.Element = n match {
    case r: CfgStmtNode =>
      // Defensive checks (intraprocedural, no records/calls)
      NoCalls.assertContainsNode(r.data)
      NoRecords.assertContainsNode(r.data)

      r.data match {
        // Rule 1：变量声明初始化为 STACK（而不是 ⊥）
        case v: AVarStmt =>
          s ++ v.declIds.map(_ -> make(STACK, Set()))

        // Assignment
        case AAssignStmt(xId: AIdentifier, rhs, loc) =>
          val xDecl = declData(xId)
          val xVal  = s(xDecl)

          // Rule 0：赋值前释放 x 的历史借用
          val s0 = statusOfV(xVal) match {
            case Some(BORROWED) =>
              setOfV(xVal).foldLeft(s) { (acc, oId) =>
                val od = declData(oId)
                val ov = acc(od)
                acc + (od -> withBorrowers(ov, setOfV(ov) - xId))
              }
            case Some(OWNS) =>
              if (setOfV(xVal).nonEmpty)
                msgErr(loc, s"cannot assign while borrowed: ${idName(xId)}")
              s
            case _ => s
          }

          rhs match {
            // Rules 2–6: x = y
            case yId: AIdentifier =>
              val yDecl = declData(yId)
              val yVal  = s0(yDecl)
              val ySt   = statusOfV(yVal)
              val ySet  = setOfV(yVal)

              ySt match {
                case Some(STACK) =>
                  write(xDecl, make(STACK, Set()), s0)

                case Some(OWNS) if ySet.isEmpty =>
                  val s1 = write(xDecl, make(OWNS, Set()), s0)
                  write(yDecl, make(DISOWNS, Set(xId)), s1)

                case Some(OWNS) =>
                  msgErr(loc, s"cannot move while borrowed: ${idName(yId)}")
                  write(xDecl, yVal, s0)

                case Some(BORROWED) =>
                  val xNew = make(BORROWED, ySet)
                  val s1   = write(xDecl, xNew, s0)
                  ySet.foldLeft(s1) { (acc, oId) =>
                    val od = declData(oId)
                    val ov = acc(od)
                    acc + (od -> withBorrowers(ov, setOfV(ov) + xId))
                  }

                case Some(DISOWNS) =>
                  msgErr(loc, s"cannot move twice: ${idName(yId)}")
                  write(xDecl, yVal, s0)

                case _ =>
                  msgWarn(loc, s"possible ownership problem: ${idName(yId)}")
                  write(xDecl, yVal, s0)
              }

            // Rule 7 & 8b: x = &y
            case AVarRef(y: AIdentifier, _) =>
              val yDecl = declData(y)
              val yVal  = s0(yDecl)
              statusOfV(yVal) match {
                case Some(OWNS) =>
                  val xNew = make(BORROWED, Set(y))
                  val yNew = withBorrowers(yVal, setOfV(yVal) + xId)
                  write(yDecl, yNew, write(xDecl, xNew, s0))
                case _ =>
                  msgErr(loc, s"borrow of moved value: ${idName(y)}")
                  val xNew = make(BORROWED, Set(y))
                  write(xDecl, xNew, s0)
              }

            // Rule 9: x = E
            case e: AExpr =>
              eval(e, s0)
              write(xDecl, vStack, s0)

            case _ => s0
          }

        case _ => s
      }

    case _ => s
  }

  override def analyze(): lattice.Element = {
    var x = lattice.bottom; var t = x
    do { t = x; x = fun(x) } while (x != t)
    msgs.printMessages()
    x
  }
}