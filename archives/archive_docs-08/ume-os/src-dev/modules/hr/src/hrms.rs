use std::collections::HashMap;

#[derive(Debug, Clone)]
pub struct Employee {
    pub id: u32,
    pub name: String,
    pub email: String,
    pub department: String,
    pub salary: f64,
    pub active: bool,
}

#[derive(Debug, Clone)]
pub struct Department {
    pub name: String,
    pub manager: String,
    pub employee_count: usize,
}

pub struct HRMS {
    employees: HashMap<u32, Employee>,
    departments: HashMap<String, Department>,
    next_id: u32,
}

impl HRMS {
    pub fn new() -> Self {
        HRMS {
            employees: HashMap::new(),
            departments: HashMap::new(),
            next_id: 1,
        }
    }

    pub fn add_employee(&mut self, name: String, email: String, department: String, salary: f64) -> u32 {
        let id = self.next_id;
        self.next_id += 1;
        
        let employee = Employee {
            id,
            name,
            email,
            department,
            salary,
            active: true,
        };
        
        self.employees.insert(id, employee);
        id
    }

    pub fn get_employee(&self, id: u32) -> Option<Employee> {
        self.employees.get(&id).cloned()
    }

    pub fn remove_employee(&mut self, id: u32) -> bool {
        self.employees.remove(&id).is_some()
    }

    pub fn list_employees(&self) -> Vec<Employee> {
        self.employees.values().cloned().collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_add_employee() {
        let mut hrms = HRMS::new();
        let id = hrms.add_employee("John Doe".to_string(), "john@example.com".to_string(), "Engineering".to_string(), 80000.0);
        assert_eq!(id, 1);
    }
}