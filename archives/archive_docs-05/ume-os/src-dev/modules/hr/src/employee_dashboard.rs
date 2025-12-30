use std::collections::HashMap;

#[derive(Debug, Clone)]
pub struct Employee {
    pub id: String,
    pub name: String,
    pub email: String,
    pub department: String,
    pub position: String,
}

#[derive(Debug, Clone)]
pub struct DashboardData {
    pub employee: Employee,
    pub leave_balance: i32,
    pub pending_requests: Vec<String>,
    pub announcements: Vec<String>,
}

pub struct EmployeePortal {
    employees: HashMap<String, Employee>,
    dashboards: HashMap<String, DashboardData>,
}

impl EmployeePortal {
    pub fn new() -> Self {
        EmployeePortal {
            employees: HashMap::new(),
            dashboards: HashMap::new(),
        }
    }

    pub fn add_employee(&mut self, employee: Employee) {
        self.employees.insert(employee.id.clone(), employee);
    }

    pub fn get_dashboard(&self, employee_id: &str) -> Option<&DashboardData> {
        self.dashboards.get(employee_id)
    }

    pub fn update_dashboard(&mut self, employee_id: String, dashboard: DashboardData) {
        self.dashboards.insert(employee_id, dashboard);
    }

    pub fn list_employees(&self) -> Vec<&Employee> {
        self.employees.values().collect()
    }
}

impl Default for EmployeePortal {
    fn default() -> Self {
        Self::new()
    }
}

pub fn get_employee(&self, employee_id: &str) -> Option<&Employee> {
    self.employees.get(employee_id)
}

pub fn create_dashboard(&mut self, employee_id: String, leave_balance: i32) {
    if let Some(employee) = self.employees.get(&employee_id).cloned() {
        let dashboard = DashboardData {
            employee,
            leave_balance,
            pending_requests: Vec::new(),
            announcements: Vec::new(),
        };
        self.dashboards.insert(employee_id, dashboard);
    }
}

pub fn add_announcement(&mut self, employee_id: &str, announcement: String) {
    if let Some(dashboard) = self.dashboards.get_mut(employee_id) {
        dashboard.announcements.push(announcement);
    }
}

pub fn add_pending_request(&mut self, employee_id: &str, request: String) {
    if let Some(dashboard) = self.dashboards.get_mut(employee_id) {
        dashboard.pending_requests.push(request);
    }
}

pub fn update_leave_balance(&mut self, employee_id: &str, balance: i32) {
    if let Some(dashboard) = self.dashboards.get_mut(employee_id) {
        dashboard.leave_balance = balance;
    }
}

pub fn get_employee_profile(&self, employee_id: &str) -> Option<EmployeeProfile> {
    self.dashboards.get(employee_id).map(|dashboard| {
        EmployeeProfile {
            employee: dashboard.employee.clone(),
            leave_balance: dashboard.leave_balance,
            pending_requests: dashboard.pending_requests.clone(),
            announcements: dashboard.announcements.clone(),
        }
    })
}

pub fn update_employee_info(&mut self, employee_id: &str, name: String, email: String, position: String) -> bool {
    if let Some(employee) = self.employees.get_mut(employee_id) {
        employee.name = name;
        employee.email = email;
        employee.position = position;
        
        if let Some(dashboard) = self.dashboards.get_mut(employee_id) {
            dashboard.employee = employee.clone();
        }
        return true;
    }
    false
}

pub fn get_employee_announcements(&self, employee_id: &str) -> Option<Vec<String>> {
    self.dashboards.get(employee_id).map(|d| d.announcements.clone())
}

pub fn remove_employee(&mut self, employee_id: &str) -> bool {
    self.employees.remove(employee_id).is_some() && self.dashboards.remove(employee_id).is_some()
}

#[derive(Debug, Clone)]
pub struct EmployeeProfile {
    pub employee: Employee,
    pub leave_balance: i32,
    pub pending_requests: Vec<String>,
    pub announcements: Vec<String>,
}