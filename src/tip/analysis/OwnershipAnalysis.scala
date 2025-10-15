package tip.analysis

import tip.ast.AstNodeData.DeclarationData
import tip.ast._
import tip.cfg.CfgOps._
import tip.cfg.{CfgNode, CfgStmtNode, ProgramCfg}
import tip.lattices.{MapLattice, OwnershipLattice}
import tip.solvers.FixpointSolvers
import tip.util.MessageHandler

import scala.collection.immutable.Set
import tip.lattices.OwnershipElement._  // 导入 Stack / Owns / DisOwns 枚举值

/**
 * Simple intraprocedural Ownership Analysis (Assignment Part 3).
 *
 * Based on Section 3 of the assignment specification.
 * Tracks ownership states for each variable:
 *   - Stack: variable holds stack value (e.g., integer)
 *   - Owns: variable uniquely owns a heap-allocated value
 *   - DisOwns: variable references a heap-allocated value but is not the owner
 *
 * Reports ownership errors and warnings for illegal dereferences:
 *   - "illegal dereference when not owner"
 *   - "dereference when may not be owner"
 */
class OwnershipAnalysis(cfg: ProgramCfg)(implicit declData: DeclarationData) extends FlowSensitiveAnalysis(true) {

  /** Lattice of ownership values (Stack, Owns, DisOwns, Top, Bottom). */
  val valuelattice = OwnershipLattice

  /** Declared variables in the current function. */
  val declaredVars: Set[ADeclaration] = cfg.nodes.flatMap(_.declaredVarsAndParams)

  /** MapLattice of abstract states: variable → ownership value. */
  val statelattice: MapLattice[ADeclaration, OwnershipLattice.type] = new MapLattice(valuelattice)

  /** Program lattice: CFG node → state map. */
  val lattice: MapLattice[CfgNode, statelattice.type] = new MapLattice(statelattice)

  /** Domain: all CFG nodes to be analyzed. */
  val domain: Set[CfgNode] = cfg.nodes

  /** Handler for collecting ownership-related errors and warnings. */
  val msgs = new MessageHandler

  /**
   * Expression evaluation according to ownership semantics.
   * (Implements “For the eval function...” from Assignment Section 3.)
   *
   * Rules:
   * • alloc e → Owns
   * • constants, binary ops → Stack
   * • dereference *x → Stack, but check ownership first
   *       - OwnershipError if definitely not Owns
   *       - OwnershipWarning if may not be Owns
   */
  def eval(exp: AExpr, env: statelattice.Element): valuelattice.Element = {
    exp match {
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
        if (valuelattice.isDefinitelyNotOwner(xval))
          msgs.message(msgs.Reason.OwnershipError, loc, s"illegal dereference when not owner: $subexp")
        else if (valuelattice.isMaybeOwner(xval))
          msgs.message(msgs.Reason.OwnershipWarning, loc, s"dereference when may not be owner: $subexp")
        else
          msgs.message(msgs.Reason.None, loc)
        valuelattice.evalStack() // dereferenced result is a stack value

      /** All other expressions → Stack. */
      case _ => valuelattice.evalStack()
    }
  }

  /** Get predecessor nodes of a given CFG node (for join). */
  def indep(n: CfgNode): Set[CfgNode] = n.pred.toSet

  /**
   * Local transfer function: implements Ownership Rules (1–3).
   *
   * Rules (Section 3 of assignment):
   *   1. vars v1,v2,... = JOIN(v)[v1→⊥,...]
   *   2. x = y (y is identifier): x→eval(y), y→yo
   *   3. x = E (E not identifier): x→eval(E)
   */
  def localTransfer(n: CfgNode, s: statelattice.Element): statelattice.Element = {
    n match {
      case r: CfgStmtNode =>

        // Defensive checks for unsupported language constructs in Part 3
        NoCalls.assertContainsNode(r.data)    // interprocedural calls not supported (not implementing Part 5 here)
        NoRecords.assertContainsNode(r.data)  // record and field operations ignored per spec

        r.data match {
          /** Rule 1: variable declaration — initialize to ⊥ (Bottom). */
          case v: AVarStmt =>
            val newVars = v.declIds.map(_ -> valuelattice.bottom)
            s ++ newVars

          /** Rules 2–3: assignment statements. */
          case AAssignStmt(id: AIdentifier, rhs, _) =>
            val decl = declData(id)
            rhs match {
              /** Rule 2: x = y, transfer ownership if y is an identifier. */
              case y: AIdentifier =>
                val o  = eval(y, s)
                val yo = if (o == valuelattice.FlatEl(Owns)) valuelattice.FlatEl(DisOwns) else o
                s + (decl -> o) + (declData(y) -> yo)

              /** Rule 3: x = E, where E is not an identifier. */
              case _ =>
                val o = eval(rhs, s)
                s + (decl -> o)
            }

          /** Other statements do not affect ownership. */
          case _ => s
        }

      case _ => s
    }
  }

  /** Compute sub-function (transfer after join). */
  def funsub(n: CfgNode, x: lattice.Element): lattice.sublattice.Element =
    localTransfer(n, join(n, x))

  /** Join function: merges predecessor states. */
  def join(n: CfgNode, o: lattice.Element): statelattice.Element = {
    val states = indep(n).map(o(_))
    states.foldLeft(statelattice.bottom)((acc, pred) => statelattice.lub(acc, pred))
  }

  /** Global fixpoint function (applies transfer function over domain). */
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
   * Runs until a stable fixpoint is reached, then prints any ownership errors or warnings.
   */
  def analyze(): lattice.Element = {
    var x = lattice.bottom
    var t = x
    do {
      t = x
      x = fun(x)
    } while (x != t)

    // Print all recorded messages at end of analysis.
    msgs.printMessages()
    x
  }
}
