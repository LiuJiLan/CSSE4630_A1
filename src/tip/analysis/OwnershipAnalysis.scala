package tip.analysis

import tip.ast.AstNodeData.DeclarationData
import tip.ast._
import tip.cfg.CfgOps._
import tip.cfg.{CfgNode, CfgStmtNode, ProgramCfg}
import tip.lattices.{MapLattice, OwnershipLattice}
import tip.solvers.FixpointSolvers
import tip.util.MessageHandler

import scala.collection.immutable.Set

class OwnershipAnalysis(cfg: ProgramCfg)(implicit declData: DeclarationData)
  extends FlowSensitiveAnalysis(true) {

  val valuelattice = OwnershipLattice
  val declaredVars: Set[ADeclaration] = cfg.nodes.flatMap(_.declaredVarsAndParams)
  val statelattice: MapLattice[ADeclaration, OwnershipLattice.type] = new MapLattice(valuelattice)
  val lattice: MapLattice[CfgNode, statelattice.type] = new MapLattice(statelattice)
  val domain: Set[CfgNode] = cfg.nodes
  val msgs = new MessageHandler

  import valuelattice._                  // Element, BorrowSet, make/withStatus/withBorrowers/statusOf/borrowersOf
  import tip.lattices.OwnershipElement._ // STACK, OWNS, DISOWNS, BORROWED, TOP

  private def read(id: AIdentifier, env: statelattice.Element): Element = env(declData(id))
  private def write(d: ADeclaration, v: Element, env: statelattice.Element) = env + (d -> v)
  private def statusOfV(v: Element) = valuelattice.statusOf(v)
  private def setOfV(v: Element) = valuelattice.borrowersOf(v)

  private def msgNone(l: Loc) = msgs.message(msgs.Reason.None, l)
  private def msgErr(l: Loc, t: String) = msgs.message(msgs.Reason.OwnershipError, l, t)
  private def msgWarn(l: Loc, t: String) = msgs.message(msgs.Reason.OwnershipWarning, l, t)

  private def vStack = make(STACK, Set())
  private def vOwns = make(OWNS, Set())
  private def vDisowns = make(DISOWNS, Set())
  private def vBorrowed = make(BORROWED, Set())

  // Rule 9 deref checks (result treated as STACK)
  def eval(e: AExpr, env: statelattice.Element): Element = e match {
    case id: AIdentifier => read(id, env)
    case _: AAlloc       => vOwns
    case _: ANumber | _: AInput | _: ABinaryOp => vStack
    case AUnaryOp(DerefOp, inner, loc) =>
      inner match {
        case y: AIdentifier =>
          statusOfV(read(y, env)) match {
            case Some(OWNS) => msgNone(loc)
            case _          => msgErr(loc, s"ownership problem: *$y")
          }; vStack
        case AUnaryOp(DerefOp, z: AIdentifier, _) =>
          statusOfV(read(z, env)) match {
            case Some(BORROWED) => msgNone(loc)
            case _              => msgErr(loc, s"ownership problem: **$z")
          }; vStack
        case es =>
          msgErr(loc, s"ownership problem: *$es"); vStack
      }
    case _ => vStack
  }

  def indep(n: CfgNode): Set[CfgNode] = n.pred.toSet
  def join(n: CfgNode, o: lattice.Element) =
    indep(n).map(o(_)).foldLeft(statelattice.bottom)((a, b) => statelattice.lub(a, b))
  def funsub(n: CfgNode, x: lattice.Element) = localTransfer(n, join(n, x))
  def fun(x: lattice.Element) =
    domain.foldLeft(lattice.bottom)((m, a) => m + (a -> localTransfer(a, join(a, x))))

  // Part3-Rule1 + Part4 Rule 0–9 (8 -> 8b)
  def localTransfer(n: CfgNode, s: statelattice.Element): statelattice.Element = n match {
    case r: CfgStmtNode =>
      NoCalls.assertContainsNode(r.data)
      NoRecords.assertContainsNode(r.data)
      r.data match {
        case v: AVarStmt =>
          s ++ v.declIds.map(_ -> valuelattice.bottom)

        case AAssignStmt(xId: AIdentifier, rhs, loc) =>
          val xDecl = declData(xId)
          val xVal  = s(xDecl)

          // Rule 0
          val s0 = statusOfV(xVal) match {
            case Some(BORROWED) =>
              setOfV(xVal).foldLeft(s) { (acc, oId) =>
                val od = declData(oId)
                val ov = acc(od)
                acc + (od -> withBorrowers(ov, setOfV(ov) - xId))
              }
            case Some(OWNS) =>
              if (setOfV(xVal).nonEmpty) msgErr(loc, s"cannot assign while borrowed: $xId"); s
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
                  msgErr(loc, s"cannot move while borrowed: $yId")
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
                  msgErr(loc, s"cannot move twice: $yId")
                  write(xDecl, yVal, s0)

                case _ =>
                  msgWarn(loc, s"possible ownership problem: $yId")
                  write(xDecl, yVal, s0)
              }

            // Rule 7 & 8b: x = &y  -> in this AST it's AVarRef(y, _)
            case AVarRef(y: AIdentifier, _) =>
              val yDecl = declData(y)
              val yVal  = s0(yDecl)
              statusOfV(yVal) match {
                case Some(OWNS) =>
                  val xNew = make(BORROWED, Set(y))
                  val yNew = withBorrowers(yVal, setOfV(yVal) + xId)
                  write(yDecl, yNew, write(xDecl, xNew, s0))
                case _ =>
                  msgErr(loc, s"borrow of moved value: $y")
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

  def analyze(): lattice.Element = {
    var x = lattice.bottom; var t = x
    do { t = x; x = fun(x) } while (x != t)
    msgs.printMessages(); x
  }
}
