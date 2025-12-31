use std::collections::HashMap;

#[derive(Clone, Debug)]
pub struct Employee {
    pub id: u32,
    pub name: String,
    pub email: String,
    pub department: String,
    pub salary: f64,
}

pub struct EmployeeManager {
    employees: HashMap<u32, Employee>,
    next_id: u32,
}

impl EmployeeManager {
    pub fn new() -> Self {
        EmployeeManager {
            employees: HashMap::new(),
            next_id: 1,
        }
    }

    pub fn add_employee(&mut self, name: String, email: String, department: String, salary: f64) -> u32 {
        let id = self.next_id;
        let employee = Employee {
            id,
            name,
            email,
            department,
            salary,
        };
        self.employees.insert(id, employee);
        self.next_id += 1;
        id
    }

    pub fn get_employee(&self, id: u32) -> Option<Employee> {
        self.employees.get(&id).cloned()
    }

    pub fn update_employee(&mut self, id: u32, name: String, email: String, department: String, salary: f64) -> bool {
        if let Some(employee) = self.employees.get_mut(&id) {
            employee.name = name;
            employee.email = email;
            employee.department = department;
            employee.salary = salary;
            true
        } else {
            false
        }
    }

    pub fn remove_employee(&mut self, id: u32) -> bool {
        self.employees.remove(&id).is_some()
    }

    pub fn list_all_employees(&self) -> Vec<Employee> {
        self.employees.values().cloned().collect()
    }

    pub fn list_by_department(&self, department: &str) -> Vec<Employee> {
        self.employees
            .values()
            .filter(|e| e.department == department)
            .cloned()
            .collect()
    }
}

impl Default for EmployeeManager {
    fn default() -> Self {
        Self::new()
    }
}