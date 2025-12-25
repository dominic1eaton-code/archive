/**
 * @license MIT
 * @brief 
 * @copyright (c) 2024 Kogi Corporation
 * @author Kogi Development Team
 */
class Payment(
    id: String,
    amount: BigDecimal,
    currency: String,
    status: String
) {
    def process(): Boolean = {
        // Process payment logic
        true
    }

    def refund(): Boolean = {
        // Refund logic
        true
    }

    override def toString: String = {
        s"Payment(id=$id, amount=$amount, currency=$currency, status=$status)"
    }
}