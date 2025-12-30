use std::collections::HashMap;
use chrono::{DateTime, Utc};

#[derive(Debug, Clone)]
pub struct Investor {
    pub id: String,
    pub name: String,
    pub email: String,
    pub phone: Option<String>,
    pub investment_amount: f64,
    pub portfolio: Vec<Investment>,
    pub created_at: DateTime<Utc>,
    pub last_contact: Option<DateTime<Utc>>,
}

#[derive(Debug, Clone)]
pub struct Investment {
    pub asset_id: String,
    pub amount: f64,
    pub date: DateTime<Utc>,
    pub status: InvestmentStatus,
}

#[derive(Debug, Clone, PartialEq)]
pub enum InvestmentStatus {
    Active,
    Completed,
    OnHold,
}

pub struct InvestorManager {
    investors: HashMap<String, Investor>,
}

impl InvestorManager {
    pub fn new() -> Self {
        InvestorManager {
            investors: HashMap::new(),
        }
    }

    pub fn add_investor(&mut self, investor: Investor) {
        self.investors.insert(investor.id.clone(), investor);
    }

    pub fn get_investor(&self, id: &str) -> Option<&Investor> {
        self.investors.get(id)
    }

    pub fn update_last_contact(&mut self, id: &str) {
        if let Some(investor) = self.investors.get_mut(id) {
            investor.last_contact = Some(Utc::now());
        }
    }

    pub fn get_all_investors(&self) -> Vec<&Investor> {
        self.investors.values().collect()
    }

    pub fn remove_investor(&mut self, id: &str) -> Option<Investor> {
        self.investors.remove(id)
    }
}

impl Default for InvestorManager {
    fn default() -> Self {
        Self::new()
    }
}