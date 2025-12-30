use std::collections::HashMap;
use chrono::{DateTime, Utc};

#[derive(Debug, Clone)]
pub struct ProcurementRequest {
    pub id: String,
    pub vendor_id: String,
    pub items: Vec<ProcurementItem>,
    pub status: RequestStatus,
    pub created_at: DateTime<Utc>,
    pub updated_at: DateTime<Utc>,
}

#[derive(Debug, Clone)]
pub struct ProcurementItem {
    pub product_id: String,
    pub quantity: u32,
    pub unit_price: f64,
    pub description: String,
}

#[derive(Debug, Clone, PartialEq)]
pub enum RequestStatus {
    Draft,
    Submitted,
    Approved,
    OrderPlaced,
    Received,
    Rejected,
}

pub struct ProcurementManager {
    requests: HashMap<String, ProcurementRequest>,
    request_counter: u32,
}

impl ProcurementManager {
    pub fn new() -> Self {
        Self {
            requests: HashMap::new(),
            request_counter: 0,
        }
    }

    pub fn create_request(
        &mut self,
        vendor_id: String,
        items: Vec<ProcurementItem>,
    ) -> String {
        self.request_counter += 1;
        let id = format!("PR-{:05}", self.request_counter);

        let request = ProcurementRequest {
            id: id.clone(),
            vendor_id,
            items,
            status: RequestStatus::Draft,
            created_at: Utc::now(),
            updated_at: Utc::now(),
        };

        self.requests.insert(id.clone(), request);
        id
    }

    pub fn update_status(&mut self, request_id: &str, status: RequestStatus) -> bool {
        if let Some(request) = self.requests.get_mut(request_id) {
            request.status = status;
            request.updated_at = Utc::now();
            return true;
        }
        false
    }

    pub fn get_request(&self, request_id: &str) -> Option<&ProcurementRequest> {
        self.requests.get(request_id)
    }

    pub fn calculate_total(&self, request_id: &str) -> Option<f64> {
        self.requests.get(request_id).map(|req| {
            req.items.iter().map(|item| item.quantity as f64 * item.unit_price).sum()
        })
    }
}