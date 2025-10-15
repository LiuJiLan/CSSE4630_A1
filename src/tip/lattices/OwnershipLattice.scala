package tip.lattices

import tip.ast.AIdentifier

object OwnershipElement extends Enumeration {
  val STACK, OWNS, DISOWNS, BORROWED, TOP = Value
}

/**
  * Ownership lattice for Part 4 (Borrow Analysis).
  * Left  : FlatLattice[OwnershipElement.Value]
  * Right : PowersetLattice[AIdentifier]
  */
object OwnershipLattice
  extends PairLattice(
    new FlatLattice[OwnershipElement.Value],
    new PowersetLattice[AIdentifier]
  ) {

  import OwnershipElement._

  type Status    = OwnershipElement.Value
  type BorrowSet = Set[AIdentifier]

  /** Construct a pair element (status, borrowers) */
  def make(status: Status, borrowers: BorrowSet): Element = {
    val leftPart: sublattice1.Element  = sublattice1.wrap(status)
    val rightPart: sublattice2.Element = borrowers.asInstanceOf[sublattice2.Element]
    (leftPart, rightPart)
  }

  /** Common lattice elements */
  val bot: Element      = bottom
  val stack: Element    = make(STACK, Set.empty)
  val owns: Element     = make(OWNS, Set.empty)
  val disowns: Element  = make(DISOWNS, Set.empty)
  val borrowed: Element = make(BORROWED, Set.empty)

  /** Extract status from the left part */
  def statusOf(e: Element): Option[Status] = e._1 match {
    case sublattice1.FlatEl(s) => Some(s)
    case _                     => None
  }

  /** Extract borrower set from the right part */
  def borrowersOf(e: Element): BorrowSet =
    e._2.asInstanceOf[BorrowSet]

  /** Replace the status part */
  def withStatus(e: Element, s: Status): Element = {
    val newLeft: sublattice1.Element = sublattice1.wrap(s)
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
