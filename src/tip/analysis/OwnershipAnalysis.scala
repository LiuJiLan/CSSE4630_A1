package tip.analysis

import tip.ast.AstNodeData.DeclarationData
import tip.ast._
import tip.cfg.CfgOps._
import tip.cfg.{CfgNode, CfgStmtNode, ProgramCfg}
import tip.lattices.{MapLattice, OwnershipLattice}
import tip.solvers.FixpointSolvers
import tip.util.MessageHandler

import scala.collection.immutable.Set
import tip.lattices.OwnershipElement._  // Stack / Owns / DisOwns

/**
 * Simple intraprocedural Ownership Analysis (Assignment Part 3).
 *
 * Tracks ownership states for each variable:
 *   - Stack: variable holds stack value (e.g., integer)
 *   - Owns: variable uniquely owns a heap-allocated value
 *   - DisOwns: variable references a heap-allocated value but is not the owner
 *
 * Reports ownership errors and warnings for illegal dereferences:
 *   - "illegal dereference when not owner"
 *   - "dereference when may not be owner"
 */
class OwnershipAnalysis(cfg: ProgramCfg)(implicit declData: DeclarationData)
  extends FlowSensitiveAnalysis(true) {

  val valuelattice = OwnershipLattice
  val declaredVars: Set[ADeclaration] = cfg.nodes.flatMap(_.declaredVarsAndParams)
  val statelattice: MapLattice[ADeclaration, OwnershipLattice.type] = new MapLattice(valuelattice)
  val lattice: MapLattice[CfgNode, statelattice.type] = new MapLattice(statelattice)
  val domain: Set[CfgNode] = cfg.nodes
  val msgs = new MessageHandler

  /** 仅返回标识符名字（避免输出 c[9:15] 这种形式） */
  private def idName(id: AIdentifier): String = id.name

  /**
   * Expression evaluation according to ownership semantics.
   */
  def eval(exp: AExpr, env: statelattice.Element): valuelattice.Element = exp match {

    /** Identifier: lookup in environment. */
    case id: AIdentifier =>
      env(declData(id))

    /** alloc e → Owns (heap allocation). */
    case _: AAlloc =>
      valuelattice.evalAlloc()

    /** constants or arithmetic → Stack. */
    case _: ANumber | _: AInput | _: ABinaryOp =>
      valuelattice.evalStack()

    /** dereference *x — must be owner, else warning or error. */
    case AUnaryOp(DerefOp, subexp, loc) =>
      val xval = eval(subexp, env)
      subexp match {
        case id: AIdentifier =>
          if (valuelattice.isDefinitelyNotOwner(xval))
            msgs.message(msgs.Reason.OwnershipError, loc,
              s"illegal dereference when not owner: ${idName(id)}")
          else if (valuelattice.isMaybeOwner(xval))
            msgs.message(msgs.Reason.OwnershipWarning, loc,
              s"dereference when may not be owner: ${idName(id)}")
          else
            msgs.message(msgs.Reason.None, loc)
        case _ =>
          if (valuelattice.isDefinitelyNotOwner(xval))
            msgs.message(msgs.Reason.OwnershipError, loc,
              s"illegal dereference when not owner: $subexp")
          else if (valuelattice.isMaybeOwner(xval))
            msgs.message(msgs.Reason.OwnershipWarning, loc,
              s"dereference when may not be owner: $subexp")
          else
            msgs.message(msgs.Reason.None, loc)
      }
      valuelattice.evalStack() // result is Stack

    /** All other expressions → Stack. */
    case _ =>
      valuelattice.evalStack()
  }

  def indep(n: CfgNode): Set[CfgNode] = n.pred.toSet

  /**
   * Local transfer: Ownership Rules (1–3)
   */
  def localTransfer(n: CfgNode, s: statelattice.Element): statelattice.Element = n match {
    case r: CfgStmtNode =>
      NoCalls.assertContainsNode(r.data)
      NoRecords.assertContainsNode(r.data)

      r.data match {
        /** Rule 1: variable declaration — initialize to ⊥. */
        case v: AVarStmt =>
          s ++ v.declIds.map(_ -> valuelattice.bottom)

        /** Rules 2–3: assignment statements. */
        case AAssignStmt(id: AIdentifier, rhs, _) =>
          val decl = declData(id)
          rhs match {
            /** Rule 2: x = y */
            case y: AIdentifier =>
              val o  = eval(y, s)
              val yo = if (o == valuelattice.FlatEl(Owns))
                         valuelattice.FlatEl(DisOwns)
                       else o
              s + (decl -> o) + (declData(y) -> yo)

            /** Rule 3: x = E */
            case _ =>
              val o = eval(rhs, s)
              s + (decl -> o)
          }

        case _ => s
      }

    case _ => s
  }

  def funsub(n: CfgNode, x: lattice.Element): lattice.sublattice.Element =
    localTransfer(n, join(n, x))

  def join(n: CfgNode, o: lattice.Element): statelattice.Element = {
    val states = indep(n).map(o(_))
    states.foldLeft(statelattice.bottom)((acc, pred) => statelattice.lub(acc, pred))
  }

  def fun(x: lattice.Element): lattice.Element = {
    FixpointSolvers.log.verb(s"In state $x")
    domain.foldLeft(lattice.bottom)((m, a) =>
      m + (a -> {
        FixpointSolvers.log.verb(s"Processing $a")
        funsub(a, x)
      })
    )
  }

  def analyze(): lattice.Element = {
    var x = lattice.bottom
    var t = x
    do {
      t = x
      x = fun(x)
    } while (x != t)
    msgs.printMessages()
    x
  }
}
