package tip.lattices

import tip.ast.AIdentifier

/**
 * CSSE4630 Assignment 1 — Part 4
 *
 * Borrow lattice for the Borrow Analysis.
 *
 * This lattice is a PairLattice composed of:
 *   - Left  : FlatLattice[BorrowElement.Value]
 *             tracks the current borrow or ownership status.
 *   - Right : PowersetLattice[AIdentifier]
 *             tracks the set of related variables:
 *               • if status = OWNS      → borrowers
 *               • if status = BORROWED  → possible owners
 *
 * It underpins the intraprocedural borrow analysis described
 * in Section 4 of the assignment specification.
 *
 * Borrow statuses (Flat domain):
 *   STACK    — variable holds a stack value (non-pointer)
 *   OWNS     — uniquely owns a heap-allocated value
 *   DISOWNS  — points to a heap-allocated value but not the owner
 *   BORROWED — immutable reference to another variable
 *   TOP      — unknown or uncertain ownership
 */
object BorrowElement extends Enumeration {
  val STACK, OWNS, DISOWNS, BORROWED, TOP = Value
}

/**
 * BorrowLattice
 *
 * Defines a pair lattice structure for borrow analysis.
 * The left component encodes the borrow/ownership status,
 * and the right component stores the set of borrowers or
 * possible owners depending on the status.
 *
 * This lattice supports the application of Rules (0–9)
 * from Section 4 of the assignment specification.
 */
object BorrowLattice
  extends PairLattice(
    new FlatLattice[BorrowElement.Value],
    new PowersetLattice[AIdentifier]
  ) {

  import BorrowElement._

  type Status    = BorrowElement.Value
  type BorrowSet = Set[AIdentifier]

  /** Constructs a pair element (status, borrowers/owners set). */
  def make(status: Status, borrowers: BorrowSet): Element = {
    val leftPart: sublattice1.Element  = sublattice1.wrap(status)
    val rightPart: sublattice2.Element = borrowers.asInstanceOf[sublattice2.Element]
    (leftPart, rightPart)
  }

  /** Predefined lattice elements for convenience. */
  val bot: Element      = bottom
  val stack: Element    = make(STACK, Set.empty)
  val owns: Element     = make(OWNS, Set.empty)
  val disowns: Element  = make(DISOWNS, Set.empty)
  val borrowed: Element = make(BORROWED, Set.empty)

  /** Extracts the status (left component) of a pair element. */
  def statusOf(e: Element): Option[Status] = e._1 match {
    case sublattice1.FlatEl(s) => Some(s)
    case _                     => None
  }

  /** Extracts the borrower or owner set (right component). */
  def borrowersOf(e: Element): BorrowSet =
    e._2.asInstanceOf[BorrowSet]

  /** Returns a new element with updated status but same borrower set. */
  def withStatus(e: Element, s: Status): Element =
    (sublattice1.wrap(s), e._2)

  /** Returns a new element with updated borrower set but same status. */
  def withBorrowers(e: Element, bs: BorrowSet): Element =
    (e._1, bs.asInstanceOf[sublattice2.Element])

  /** Readable string representation for debugging. */
  override def toString: String =
    "BorrowLattice(Flat(Status), Powerset(Identifiers))"
}
