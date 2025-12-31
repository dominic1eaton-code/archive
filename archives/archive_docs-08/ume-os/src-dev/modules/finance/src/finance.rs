use std::collections::HashMap;
use chrono::{DateTime, Utc};

#[derive(Debug, Clone)]
pub struct Transaction {
    pub id: String,
    pub account_id: String,
    pub amount: f64,
    pub transaction_type: TransactionType,
    pub description: String,
    pub timestamp: DateTime<Utc>,
}

#[derive(Debug, Clone)]
pub enum TransactionType {
    Debit,
    Credit,
    Transfer,
}

#[derive(Debug)]
pub struct Account {
    pub id: String,
    pub name: String,
    pub balance: f64,
    pub currency: String,
}

#[derive(Debug)]
pub struct FinanceManager {
    accounts: HashMap<String, Account>,
    transactions: Vec<Transaction>,
}

impl FinanceManager {
    pub fn new() -> Self {
        FinanceManager {
            accounts: HashMap::new(),
            transactions: Vec::new(),
        }
    }

    pub fn create_account(&mut self, id: String, name: String, currency: String) -> Result<(), String> {
        if self.accounts.contains_key(&id) {
            return Err("Account already exists".to_string());
        }
        self.accounts.insert(id, Account { id: id.clone(), name, balance: 0.0, currency });
        Ok(())
    }

    pub fn record_transaction(&mut self, transaction: Transaction) -> Result<(), String> {
        if !self.accounts.contains_key(&transaction.account_id) {
            return Err("Account not found".to_string());
        }
        self.transactions.push(transaction);
        Ok(())
    }

    pub fn get_balance(&self, account_id: &str) -> Result<f64, String> {
        self.accounts.get(account_id)
            .map(|acc| acc.balance)
            .ok_or_else(|| "Account not found".to_string())
    }

    pub fn get_transactions(&self, account_id: &str) -> Vec<&Transaction> {
        self.transactions.iter().filter(|t| t.account_id == account_id).collect()
    }
}