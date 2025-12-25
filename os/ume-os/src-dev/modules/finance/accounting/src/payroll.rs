use std::collections::HashMap;

#[derive(Debug, Clone)]
pub struct Employee {
    id: u32,
    name: String,
    salary: f64,
    department: String,
}

#[derive(Debug, Clone)]
pub struct PayrollRecord {
    employee_id: u32,
    gross_salary: f64,
    tax: f64,
    net_salary: f64,
    payment_date: String,
}

pub struct PayrollManager {
    employees: HashMap<u32, Employee>,
    payroll_records: Vec<PayrollRecord>,
}

impl PayrollManager {
    pub fn new() -> Self {
        PayrollManager {
            employees: HashMap::new(),
            payroll_records: Vec::new(),
        }
    }

    pub fn add_employee(&mut self, employee: Employee) {
        self.employees.insert(employee.id, employee);
    }

    pub fn process_payroll(&mut self, employee_id: u32, payment_date: String) -> Result<PayrollRecord, String> {
        let employee = self.employees
            .get(&employee_id)
            .ok_or("Employee not found")?;

        let gross_salary = employee.salary;
        let tax = gross_salary * 0.15; // 15% tax
        let net_salary = gross_salary - tax;

        let record = PayrollRecord {
            employee_id,
            gross_salary,
            tax,
            net_salary,
            payment_date,
        };

        self.payroll_records.push(record.clone());
        Ok(record)
    }

    pub fn get_employee(&self, id: u32) -> Option<&Employee> {
        self.employees.get(&id)
    }

    pub fn payroll_history(&self, employee_id: u32) -> Vec<&PayrollRecord> {
        self.payroll_records
            .iter()
            .filter(|r| r.employee_id == employee_id)
            .collect()
    }
}