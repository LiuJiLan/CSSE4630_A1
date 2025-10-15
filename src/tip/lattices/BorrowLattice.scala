package tip.lattices

import tip.ast.AIdentifier

object BorrowElement extends Enumeration {
  val STACK, OWNS, DISOWNS, BORROWED, TOP = Value
}

/**
  * Borrow lattice for Part 4 (Borrow Analysis).
  * Left  : FlatLattice[BorrowElement.Value]
  * Right : PowersetLattice[AIdentifier]   // set of borrowers (or possible owners if BORROWED)
  */
object BorrowLattice
  extends PairLattice(
    new FlatLattice[BorrowElement.Value],
    new PowersetLattice[AIdentifier]
  ) {

  import BorrowElement._

  type Status    = BorrowElement.Value
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
  def withStatus(e: Element, s: Status): Element =
    (sublattice1.wrap(s), e._2)

  /** Replace the borrower set */
  def withBorrowers(e: Element, bs: BorrowSet): Element =
    (e._1, bs.asInstanceOf[sublattice2.Element])

  override def toString: String =
    "BorrowLattice(Flat(Status), Powerset(Identifiers))"
}
