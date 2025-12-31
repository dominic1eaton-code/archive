use std::collections::HashMap;
use std::time::{SystemTime, UNIX_EPOCH};

#[derive(Debug, Clone, PartialEq)]
pub enum OperationStatus {
    Pending,
    InProgress,
    Completed,
    Failed,
}

#[derive(Debug, Clone)]
pub struct Operation {
    pub id: String,
    pub name: String,
    pub status: OperationStatus,
    pub created_at: u64,
    pub updated_at: u64,
    pub assigned_to: Option<String>,
}

#[derive(Debug, Clone)]
pub struct Resource {
    pub id: String,
    pub name: String,
    pub resource_type: String,
    pub available: bool,
}

pub struct OperationsManager {
    operations: HashMap<String, Operation>,
    resources: HashMap<String, Resource>,
}

impl OperationsManager {
    pub fn new() -> Self {
        OperationsManager {
            operations: HashMap::new(),
            resources: HashMap::new(),
        }
    }

    pub fn create_operation(&mut self, id: String, name: String) -> Result<(), String> {
        if self.operations.contains_key(&id) {
            return Err("Operation already exists".to_string());
        }

        let now = current_timestamp();
        let operation = Operation {
            id: id.clone(),
            name,
            status: OperationStatus::Pending,
            created_at: now,
            updated_at: now,
            assigned_to: None,
        };

        self.operations.insert(id, operation);
        Ok(())
    }

    pub fn update_status(&mut self, id: &str, status: OperationStatus) -> Result<(), String> {
        match self.operations.get_mut(id) {
            Some(op) => {
                op.status = status;
                op.updated_at = current_timestamp();
                Ok(())
            }
            None => Err("Operation not found".to_string()),
        }
    }

    pub fn assign_operation(&mut self, id: &str, assignee: String) -> Result<(), String> {
        match self.operations.get_mut(id) {
            Some(op) => {
                op.assigned_to = Some(assignee);
                op.updated_at = current_timestamp();
                Ok(())
            }
            None => Err("Operation not found".to_string()),
        }
    }

    pub fn add_resource(&mut self, resource: Resource) {
        self.resources.insert(resource.id.clone(), resource);
    }

    pub fn get_operation(&self, id: &str) -> Option<&Operation> {
        self.operations.get(id)
    }

    pub fn list_operations(&self) -> Vec<&Operation> {
        self.operations.values().collect()
    }

    pub fn get_operations_by_status(&self, status: OperationStatus) -> Vec<&Operation> {
        self.operations
            .values()
            .filter(|op| op.status == status)
            .collect()
    }
}

fn current_timestamp() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_secs()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_create_operation() {
        let mut manager = OperationsManager::new();
        assert!(manager
            .create_operation("op1".to_string(), "Task 1".to_string())
            .is_ok());
        assert!(manager.get_operation("op1").is_some());
    }

    #[test]
    fn test_update_status() {
        let mut manager = OperationsManager::new();
        manager
            .create_operation("op1".to_string(), "Task 1".to_string())
            .unwrap();
        assert!(manager
            .update_status("op1", OperationStatus::InProgress)
            .is_ok());
    }
}