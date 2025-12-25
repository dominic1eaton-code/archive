use std::collections::HashMap;
use chrono::{DateTime, Utc};

#[derive(Clone, Debug)]
pub struct Campaign {
    pub id: String,
    pub name: String,
    pub description: String,
    pub status: CampaignStatus,
    pub created_at: DateTime<Utc>,
    pub budget: f64,
}

#[derive(Clone, Debug, PartialEq)]
pub enum CampaignStatus {
    Draft,
    Active,
    Paused,
    Completed,
}

#[derive(Clone, Debug)]
pub struct Lead {
    pub id: String,
    pub name: String,
    pub email: String,
    pub campaign_id: String,
    pub created_at: DateTime<Utc>,
}

pub struct MarketingManager {
    campaigns: HashMap<String, Campaign>,
    leads: HashMap<String, Lead>,
}

impl MarketingManager {
    pub fn new() -> Self {
        Self {
            campaigns: HashMap::new(),
            leads: HashMap::new(),
        }
    }

    pub fn create_campaign(&mut self, id: String, name: String, description: String, budget: f64) -> Campaign {
        let campaign = Campaign {
            id: id.clone(),
            name,
            description,
            status: CampaignStatus::Draft,
            created_at: Utc::now(),
            budget,
        };
        self.campaigns.insert(id, campaign.clone());
        campaign
    }

    pub fn add_lead(&mut self, id: String, name: String, email: String, campaign_id: String) -> Lead {
        let lead = Lead {
            id: id.clone(),
            name,
            email,
            campaign_id,
            created_at: Utc::now(),
        };
        self.leads.insert(id, lead.clone());
        lead
    }

    pub fn get_campaign(&self, id: &str) -> Option<Campaign> {
        self.campaigns.get(id).cloned()
    }

    pub fn update_campaign_status(&mut self, id: &str, status: CampaignStatus) -> bool {
        if let Some(campaign) = self.campaigns.get_mut(id) {
            campaign.status = status;
            true
        } else {
            false
        }
    }

    pub fn list_campaigns(&self) -> Vec<Campaign> {
        self.campaigns.values().cloned().collect()
    }

    pub fn list_leads(&self, campaign_id: &str) -> Vec<Lead> {
        self.leads
            .values()
            .filter(|lead| lead.campaign_id == campaign_id)
            .cloned()
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_create_campaign() {
        let mut manager = MarketingManager::new();
        let campaign = manager.create_campaign(
            "camp1".to_string(),
            "Summer Sale".to_string(),
            "Summer promotion".to_string(),
            5000.0,
        );
        assert_eq!(campaign.name, "Summer Sale");
        assert_eq!(campaign.status, CampaignStatus::Draft);
    }
}