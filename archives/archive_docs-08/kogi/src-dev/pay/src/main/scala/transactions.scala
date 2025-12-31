/**
 * @license MIT
 * @brief 
 * @copyright (c) 2024 Kogi Corporation
 * @author Kogi Development Team
 */
case class Transaction(
    id: String,
    amount: BigDecimal,
    currency: String,
    transactionType: String,
    status: String,
    timestamp: Long,
    description: Option[String] = None
)

class TransactionManager {
    private var transactions: List[Transaction] = List()

    def addTransaction(transaction: Transaction): Unit = {
        transactions = transactions :+ transaction
    }

    def getTransaction(id: String): Option[Transaction] = {
        transactions.find(_.id == id)
    }

    def getTransactionsByType(transactionType: String): List[Transaction] = {
        transactions.filter(_.transactionType == transactionType)
    }

    def getTotalAmount(currency: String): BigDecimal = {
        transactions
            .filter(_.currency == currency)
            .map(_.amount)
            .sum
    }

    def listAllTransactions: List[Transaction] = transactions
}