package tip.util

import tip.ast.Loc

/**
 * A class for remembering the latest message for each interesting location.
 *
 * Note: most analyses make multiple iterations, so will visit a given CFG node
 * multiple times, with increasingly accurate information each time.
 * We only want to print the message from the LAST (most accurate) of these iterations.
 *
 * So on EVERY iteration, for EVERY location that might need an error or warning message,
 * you should send an updated message to this message handler.
 * Use Reason.None when no message is needed.
 *
 * This handler will remember the most recent message, and when you reach the end
 * of your analysis and call printMessages(level), it will print all the messages
 * at that given level or above.
 */
class MessageHandler {
  object Reason extends Enumeration {
    type Reason = Value
    val None, OwnershipError, OwnershipWarning, Error, Warning, Info = Value
  }

  private val messages = collection.mutable.LinkedHashMap[Loc, (Reason.Reason, String)]()

  /**
   * Record a message for the given location.
   *
   *  Use level Reason.None if no message is needed or you want to clear previous messages for this location.
   */
  def message(reason: Reason.Reason, key: Loc, msg: String = ""): Unit = {
    if (reason != Reason.None && msg.isEmpty) {
      throw new IllegalArgumentException(s"Missing message for reason ${reason}")
    }
    messages(key) = (reason, msg)
  }

  def clearMessages() = messages.clear()

  /**
   * Print all the important error messages, sorted by line/column number.
   *
   * This ignores all messages with reason None.
   * It prints all messages with reasons up to maxLevel, which defaults
   * to Reason.Warning.  So by default, just errors and warnings will be printed.
   *
   * Set maxLevel to Reason.Info if you want to print ALL messages (except Reason.None).
   *
   * @param maxLevel
   */
  def printMessages(maxLevel: Reason.Reason = Reason.Warning) = {
    for (key <- messages.keys.toList.sortWith((a,b) =>
      a.line < b.line || (a.line == b.line && a.col < b.col))) {
      val (level,msg) = messages(key)
      if (level != Reason.None && level <= maxLevel)
        println("[%s] line:%s  %s".format(level, key, msg))
    }
  }
}

