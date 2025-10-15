package tip.lattices

import tip.ast.AIdentifier

object OwnershipElement extends Enumeration {
  val STACK, OWNS, DISOWNS, BORROWED, TOP = Value
}

/**
  * Ownership lattice for Part 4 (Borrow Analysis).
  *
  * Left  : FlatLattice[OwnershipElement.Value]
  * Right : PowersetLattice[AIdentifier]
  *
  * Combines the two using PairLattice.
  */
object OwnershipLattice
  extends PairLattice(
    new FlatLattice[OwnershipElement.Value],
    new PowersetLattice[AIdentifier]
  ) {

  import OwnershipElement._

  // Local aliases for convenience
  private val leftFlat  = sublattice1.asInstanceOf[FlatLattice[OwnershipElement.Value]]
  private val rightSet  = sublattice2.asInstanceOf[PowersetLattice[AIdentifier]]

  type Status    = OwnershipElement.Value
  type BorrowSet = Set[AIdentifier]

  /** Build a pair element (status, borrow set) */
  def make(status: Status, borrowers: BorrowSet): Element = {
    val leftPart: sublattice1.Element = leftFlat.FlatEl(status).asInstanceOf[sublattice1.Element]
    val rightPart: sublattice2.Element = borrowers.asInstanceOf[sublattice2.Element]
    (leftPart, rightPart)
  }

  /** Common lattice elements */
  val bot: Element      = bottom
  val stack: Element    = make(STACK, Set.empty)
  val owns: Element     = make(OWNS, Set.empty)
  val disowns: Element  = make(DISOWNS, Set.empty)
  val borrowed: Element = make(BORROWED, Set.empty)

  /** Extract status from a lattice element (if FlatEl) */
  def statusOf(e: Element): Option[Status] = e._1 match {
    case leftFlat.FlatEl(s) => Some(s)
    case _                  => None
  }

  /** Extract borrower set from a lattice element */
  def borrowersOf(e: Element): BorrowSet = e._2.asInstanceOf[BorrowSet]

  /** Replace the status part */
  def withStatus(e: Element, s: Status): Element = {
    val newLeft: sublattice1.Element = leftFlat.FlatEl(s).asInstanceOf[sublattice1.Element]
    (newLeft, e._2)
  }

  /** Replace the borrower set */
  def withBorrowers(e: Element, bs: BorrowSet): Element = {
    val newRight: sublattice2.Element = bs.asInstanceOf[sublattice2.Element]
    (e._1, newRight)
  }

  override def toString: String =
    "OwnershipLattice(Flat(Status), Powerset(Identifiers))"
}
