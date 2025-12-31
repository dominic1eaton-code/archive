/**
 * @license MIT
 * @brief 
 * @copyright (c) 2024 Kogi Corporation
 * @author Kogi Development Team
 */
case class Transaction(id: String, description: String, amount: Double, date: String, category: String)

class FinancesTracker {
    private var transactions: List[Transaction] = List()

    def addTransaction(transaction: Transaction): Unit = {
        transactions = transactions :+ transaction
    }

    def removeTransaction(id: String): Unit = {
        transactions = transactions.filterNot(_.id == id)
    }

    def getTransactions: List[Transaction] = transactions

    def getTotalExpenses: Double = {
        transactions.filter(_.amount < 0).map(_.amount).sum.abs
    }

    def getTotalIncome: Double = {
        transactions.filter(_.amount > 0).map(_.amount).sum
    }

    def getBalance: Double = {
        transactions.map(_.amount).sum
    }

    def getByCategory(category: String): List[Transaction] = {
        transactions.filter(_.category == category)
    }
}

def generateReport: String = {
    val totalIncome = getTotalIncome
    val totalExpenses = getTotalExpenses
    val balance = getBalance
    val categories = transactions.map(_.category).distinct
    
    val categoryBreakdown = categories.map { cat =>
        val total = getByCategory(cat).map(_.amount).sum
        s"$cat: $total"
    }.mkString("\n")
    
    s"""
       |=== Financial Report ===
       |Total Income: $$${totalIncome}
       |Total Expenses: $$${totalExpenses}
       |Balance: $$${balance}
       |
       |By Category:
       |$categoryBreakdown
       |""".stripMargin
}

def main(args: Array[String]): Unit = {
    val tracker = new FinancesTracker()
    
    tracker.addTransaction(Transaction("1", "Salary", 5000, "2024-01-15", "Income"))
    tracker.addTransaction(Transaction("2", "Groceries", -150, "2024-01-16", "Food"))
    tracker.addTransaction(Transaction("3", "Electric Bill", -80, "2024-01-17", "Utilities"))
    tracker.addTransaction(Transaction("4", "Freelance Work", 1200, "2024-01-18", "Income"))
    tracker.addTransaction(Transaction("5", "Gas", -50, "2024-01-19", "Transportation"))
    
    println(tracker.generateReport)
}