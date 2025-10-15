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
 * CSSE4630 Assignment 1 — Part 3
 *
 * Simple intraprocedural Ownership Analysis.
 *
 * Based on Section 3 of the assignment specification.
 * Tracks ownership state for each variable:
 *   - Stack   → holds a stack value (e.g., integer)
 *   - Owns    → uniquely owns a heap-allocated value
 *   - DisOwns → references a heap value but is not the owner
 *
 * Reports ownership errors and warnings for illegal dereferences:
 *   - OwnershipError  → "illegal dereference when not owner: x"
 *   - OwnershipWarning → "dereference when may not be owner: x"
 *
 * Rules implemented:
 *   Rule 1: variable declarations
 *   Rule 2: assignments of identifiers
 *   Rule 3: assignments of general expressions
 *
 * The analysis runs intraprocedurally (no function calls or records).
 */
class OwnershipAnalysis(cfg: ProgramCfg)(implicit declData: DeclarationData)
  extends FlowSensitiveAnalysis(true) {

  /** Lattice of ownership values. */
  val valuelattice = OwnershipLattice

  /** Declared variables in current function (domain of analysis). */
  val declaredVars: Set[ADeclaration] = cfg.nodes.flatMap(_.declaredVarsAndParams)

  /** Map-lattice: variable → ownership value. */
  val statelattice: MapLattice[ADeclaration, OwnershipLattice.type] =
    new MapLattice(valuelattice)

  /** Program lattice: CFG node → abstract state. */
  val lattice: MapLattice[CfgNode, statelattice.type] =
    new MapLattice(statelattice)

  /** All nodes in the control-flow graph. */
  val domain: Set[CfgNode] = cfg.nodes

  /** Message handler for recording and printing errors/warnings. */
  val msgs = new MessageHandler

  /** Helper to extract plain variable name for messages. */
  private def idName(id: AIdentifier): String = id.name

  /**
   * eval(exp, env)
   *
   * Evaluates expressions under ownership semantics (Section 3).
   *
   * According to the assignment:
   *   • alloc e → Owns
   *   • constants, binary ops → Stack
   *   • dereference *x:
   *        - if x definitely not Owns → error "illegal dereference when not owner: x"
   *        - if x may not be Owns (Top) → warning "dereference when may not be owner: x"
   *        - otherwise (x definitely Owns) → no message
   *   • result of *x is Stack
   */
  def eval(exp: AExpr, env: statelattice.Element): valuelattice.Element = exp match {

    /** Identifier: lookup its ownership value in the environment. */
    case id: AIdentifier =>
      env(declData(id))

    /** alloc e → Owns (heap allocation). */
    case _: AAlloc =>
      valuelattice.evalAlloc()

    /** constants or arithmetic operations → Stack. */
    case _: ANumber | _: AInput | _: ABinaryOp =>
      valuelattice.evalStack()

    /** dereference *x → must check ownership (For the eval function...). */
    case AUnaryOp(DerefOp, subexp, loc) =>
      val xval = eval(subexp, env)
      subexp match {
        /** *id form — use variable name in messages. */
        case id: AIdentifier =>
          if (valuelattice.isDefinitelyNotOwner(xval))
            msgs.message(msgs.Reason.OwnershipError, loc,
              s"illegal dereference when not owner: ${idName(id)}")
          else if (valuelattice.isMaybeOwner(xval))
            msgs.message(msgs.Reason.OwnershipWarning, loc,
              s"dereference when may not be owner: ${idName(id)}")
          else
            msgs.message(msgs.Reason.None, loc)

        /** *E (non-identifier) form — generic expression case. */
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
      // Result of dereference is always a stack value.
      valuelattice.evalStack()

    /** All other expressions evaluate to Stack. */
    case _ =>
      valuelattice.evalStack()
  }

  /** Returns the predecessor nodes of n (for JOIN). */
  def indep(n: CfgNode): Set[CfgNode] = n.pred.toSet

  /**
   * Local transfer function.
   *
   * Implements Ownership Rules (1–3) from Section 3:
   *
   *   Rule 1. vars v1,v2,… = JOIN(v)[v1→⊥, v2→⊥, …]
   *   Rule 2. x = y → JOIN(v)[x→eval(y), y→yo],
   *           where yo = if eval(y)=Owns then DisOwns else eval(y)
   *   Rule 3. x = E (E not identifier) → JOIN(v)[x→eval(E)]
   */
  def localTransfer(n: CfgNode, s: statelattice.Element): statelattice.Element = n match {
    case r: CfgStmtNode =>
      // Defensive checks: disallow calls and records (Part 3 scope).
      NoCalls.assertContainsNode(r.data)
      NoRecords.assertContainsNode(r.data)

      r.data match {

        /** Rule 1: variable declaration — initialize to Bottom (⊥). */
        case v: AVarStmt =>
          s ++ v.declIds.map(_ -> valuelattice.bottom)

        /** Rules 2–3: assignment statement. */
        case AAssignStmt(id: AIdentifier, rhs, _) =>
          val decl = declData(id)
          rhs match {

            /** Rule 2: assignment from another variable (x = y). */
            case y: AIdentifier =>
              val o  = eval(y, s)
              // if y was Owns → y becomes DisOwns, otherwise unchanged
              val yo = if (o == valuelattice.FlatEl(Owns))
                valuelattice.FlatEl(DisOwns)
              else o
              s + (decl -> o) + (declData(y) -> yo)

            /** Rule 3: assignment from general expression (x = E). */
            case _ =>
              val o = eval(rhs, s)
              s + (decl -> o)
          }

        /** Other statements do not affect ownership. */
        case _ =>
          s
      }

    case _ =>
      s
  }

  /** Sub-function: applies local transfer after join. */
  def funsub(n: CfgNode, x: lattice.Element): lattice.sublattice.Element =
    localTransfer(n, join(n, x))

  /** Join function: merges all predecessor states. */
  def join(n: CfgNode, o: lattice.Element): statelattice.Element = {
    val states = indep(n).map(o(_))
    states.foldLeft(statelattice.bottom)((acc, pred) => statelattice.lub(acc, pred))
  }

  /** Fixpoint function: applies transfer to all nodes. */
  def fun(x: lattice.Element): lattice.Element = {
    FixpointSolvers.log.verb(s"In state $x")
    domain.foldLeft(lattice.bottom)((m, a) =>
      m + (a -> {
        FixpointSolvers.log.verb(s"Processing $a")
        funsub(a, x)
      })
    )
  }

  /**
   * Main analysis entry point (Kleene fixpoint iteration).
   * Runs until a stable fixpoint is reached,
   * then prints any ownership errors or warnings.
   */
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
