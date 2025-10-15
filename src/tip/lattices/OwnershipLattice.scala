package tip.lattices

import tip.lattices.FlatLattice

/**
 * CSSE4630 Assignment 1 — Part 3
 *
 * Ownership lattice for Simple Ownership Analysis.
 *
 * This flat lattice tracks the ownership status of variables:
 *   - Stack:   variable holds a stack value (non-pointer, e.g., integer)
 *   - Owns:    variable uniquely owns a heap-allocated value
 *   - DisOwns: variable points to a heap-allocated value but is not the owner
 *
 * The lattice shape:
 *
 *          Top
 *        /  |  \
 *     Stack Owns DisOwns
 *        \  |  /
 *          Bot
 *
 * Used by OwnershipAnalysis (Part 3) to determine whether
 * a variable owns, disowns, or merely references a heap object.
 */
object OwnershipElement extends Enumeration {
  val Stack, Owns, DisOwns = Value
}

/**
 * Flat lattice of ownership elements.
 *
 * Provides helper functions for `eval` and ownership checks
 * as defined in the assignment specification (Section 3).
 */
object OwnershipLattice extends FlatLattice[OwnershipElement.Value] {

  import OwnershipElement._

  /** Optional lookup map for ordering or debugging. */
  private val ownershipValues: Map[Element, Int] =
    Map(Bot -> 0, FlatEl(Stack) -> 1, FlatEl(DisOwns) -> 2, FlatEl(Owns) -> 3, Top -> 4)

  /**
   * Evaluation helpers.
   *
   * From the specification (Section 3, “For the eval function”):
   *   • alloc e → Owns
   *   • constants and binary operators → Stack
   *   • dereference *x → Stack (but requires ownership checks)
   */

  /** Returns element representing heap allocation (alloc e → Owns). */
  def evalAlloc(): Element = FlatEl(Owns)

  /** Returns element representing constants and non-pointer expressions (→ Stack). */
  def evalStack(): Element = FlatEl(Stack)

  /**
   * Ownership predicates.
   *
   * From the specification (Section 3, “For the eval function”):
   * The dereference operator *x must check that x is Owns.
   * Otherwise:
   *   - If x is definitely not Owns → OwnershipError (“illegal dereference when not owner”)
   *   - If x may not be Owns (Top) → OwnershipWarning (“dereference when may not be owner”)
   *   - If x is definitely Owns → safe dereference (no message)
   *
   * These checks are implemented by OwnershipAnalysis.eval.
   */

  /** True if the variable definitely owns the heap object. */
  def isDefinitelyOwner(e: Element): Boolean = e == FlatEl(Owns)

  /** True if the variable definitely does not own (Stack or DisOwns). */
  def isDefinitelyNotOwner(e: Element): Boolean =
    e == FlatEl(Stack) || e == FlatEl(DisOwns)

  /** True if the variable’s ownership is uncertain (Top). */
  def isMaybeOwner(e: Element): Boolean = e == Top
}
