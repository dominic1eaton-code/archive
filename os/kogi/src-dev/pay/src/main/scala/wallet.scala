/**
 * @license MIT
 * @brief 
 * @copyright (c) 2024 Kogi Corporation
 * @author Kogi Development Team
 */
case class Wallet(id: String, balance: BigDecimal, currency: String = "USD")

case class Transaction(id: String, walletId: String, amount: BigDecimal, description: String, timestamp: Long)

class WalletManager {
    private var wallets: Map[String, Wallet] = Map()
    private var transactions: List[Transaction] = List()

    def createWallet(id: String, initialBalance: BigDecimal = BigDecimal(0)): Wallet = {
        val wallet = Wallet(id, initialBalance)
        wallets = wallets + (id -> wallet)
        wallet
    }

    def getWallet(id: String): Option[Wallet] = wallets.get(id)

    def deposit(walletId: String, amount: BigDecimal): Either[String, Wallet] = {
        if (amount <= 0) return Left("Amount must be positive")
        
        wallets.get(walletId) match {
            case Some(wallet) =>
                val updated = wallet.copy(balance = wallet.balance + amount)
                wallets = wallets + (walletId -> updated)
                recordTransaction(walletId, amount, "Deposit")
                Right(updated)
            case None => Left("Wallet not found")
        }
    }

    def withdraw(walletId: String, amount: BigDecimal): Either[String, Wallet] = {
        if (amount <= 0) return Left("Amount must be positive")
        
        wallets.get(walletId) match {
            case Some(wallet) if wallet.balance >= amount =>
                val updated = wallet.copy(balance = wallet.balance - amount)
                wallets = wallets + (walletId -> updated)
                recordTransaction(walletId, -amount, "Withdrawal")
                Right(updated)
            case Some(_) => Left("Insufficient funds")
            case None => Left("Wallet not found")
        }
    }

    private def recordTransaction(walletId: String, amount: BigDecimal, description: String): Unit = {
        val tx = Transaction(java.util.UUID.randomUUID().toString, walletId, amount, description, System.currentTimeMillis())
        transactions = transactions :+ tx
    }

    def getTransactionHistory(walletId: String): List[Transaction] = 
        transactions.filter(_.walletId == walletId)
}

class DigitalWallet(initialBalance: Double = 0.0) {
    private var balance: Double = initialBalance
    private val transactions: scala.collection.mutable.ListBuffer[Transaction] = scala.collection.mutable.ListBuffer()

    case class Transaction(id: String, amount: Double, transactionType: String, timestamp: Long)

    def deposit(amount: Double): Boolean = {
        if (amount > 0) {
            balance += amount
            transactions += Transaction(java.util.UUID.randomUUID().toString, amount, "DEPOSIT", System.currentTimeMillis())
            true
        } else false
    }

    def withdraw(amount: Double): Boolean = {
        if (amount > 0 && amount <= balance) {
            balance -= amount
            transactions += Transaction(java.util.UUID.randomUUID().toString, amount, "WITHDRAWAL", System.currentTimeMillis())
            true
        } else false
    }

    def transfer(amount: Double, recipient: DigitalWallet): Boolean = {
        if (this.withdraw(amount)) {
            recipient.deposit(amount)
            true
        } else false
    }

    def getBalance: Double = balance

    def getTransactionHistory: List[Transaction] = transactions.toList

    def checkBalance: String = s"Current Balance: $$${String.format("%.2f", balance)}"
}