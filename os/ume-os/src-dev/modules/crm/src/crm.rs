use std::collections::HashMap;
use std::error::Error;

#[derive(Debug, Clone)]
pub struct Customer {
    pub id: u32,
    pub name: String,
    pub email: String,
    pub phone: String,
}

#[derive(Debug, Clone)]
pub struct Interaction {
    pub id: u32,
    pub customer_id: u32,
    pub note: String,
    pub date: String,
}

pub struct CRM {
    customers: HashMap<u32, Customer>,
    interactions: HashMap<u32, Interaction>,
    next_customer_id: u32,
    next_interaction_id: u32,
}

impl CRM {
    pub fn new() -> Self {
        CRM {
            customers: HashMap::new(),
            interactions: HashMap::new(),
            next_customer_id: 1,
            next_interaction_id: 1,
        }
    }

    pub fn add_customer(&mut self, name: String, email: String, phone: String) -> u32 {
        let id = self.next_customer_id;
        self.customers.insert(id, Customer { id, name, email, phone });
        self.next_customer_id += 1;
        id
    }

    pub fn get_customer(&self, id: u32) -> Option<&Customer> {
        self.customers.get(&id)
    }

    pub fn add_interaction(&mut self, customer_id: u32, note: String, date: String) -> Result<u32, Box<dyn Error>> {
        if !self.customers.contains_key(&customer_id) {
            return Err("Customer not found".into());
        }
        let id = self.next_interaction_id;
        self.interactions.insert(id, Interaction { id, customer_id, note, date });
        self.next_interaction_id += 1;
        Ok(id)
    }

    pub fn get_customer_interactions(&self, customer_id: u32) -> Vec<&Interaction> {
        self.interactions
            .values()
            .filter(|i| i.customer_id == customer_id)
            .collect()
    }
}