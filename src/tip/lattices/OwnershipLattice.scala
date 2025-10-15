package tip.lattices

import tip.lattices.FlatLattice

/**
 * Enumeration for ownership elements.
 * These represent the possible ownership statuses of variables.
 */
object OwnershipElement extends Enumeration {
  val Stack, Owns, DisOwns = Value
}

/**
 * The Ownership Lattice.
 *
 * Flat lattice:
 *          Top
 *        /  |  \
 *     Stack Owns DisOwns
 *        \  |  /
 *          Bot
 *
 * This lattice tracks whether a variable:
 *  - Stack: holds a stack value (non-pointer, e.g., int)
 *  - Owns: uniquely owns a heap-allocated value
 *  - DisOwns: points to a heap-allocated value, but is *not* the owner
 */
object OwnershipLattice extends FlatLattice[OwnershipElement.Value] {

  import OwnershipElement._

  /** Map used for lookup convenience if needed */
  private val ownershipValues: Map[Element, Int] =
    Map(Bot -> 0, FlatEl(Stack) -> 1, FlatEl(DisOwns) -> 2, FlatEl(Owns) -> 3, Top -> 4)

  /** Evaluation helper: used by OwnershipAnalysis.eval */
  def evalAlloc(): Element = FlatEl(Owns)

  /** Evaluation helper: for constants and non-pointer expressions */
  def evalStack(): Element = FlatEl(Stack)

  /** Helper predicates for dereference checks */
  def isDefinitelyOwner(e: Element): Boolean = e == FlatEl(Owns)
  def isDefinitelyNotOwner(e: Element): Boolean = e == FlatEl(Stack) || e == FlatEl(DisOwns)
  def isMaybeOwner(e: Element): Boolean = e == Top
}
