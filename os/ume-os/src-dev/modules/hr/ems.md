# employee management system
Skip to content
You said:
create an employee management system in rust
ChatGPT said:
Sure! I can help you design a basic Employee Management System in Rust. We'll keep it simple but functional: you can add, remove, update, and list employees. Later, you could extend it with file storage, databases, or even a web API.

Here’s a working example:

use std::io;
use std::collections::HashMap;

#[derive(Debug, Clone)]
struct Employee {
    id: u32,
    name: String,
    department: String,
    salary: f64,
}

struct EmployeeManager {
    employees: HashMap<u32, Employee>,
}

impl EmployeeManager {
    fn new() -> Self {
        EmployeeManager {
            employees: HashMap::new(),
        }
    }

    fn add_employee(&mut self, employee: Employee) {
        self.employees.insert(employee.id, employee);
    }

    fn remove_employee(&mut self, id: u32) {
        if self.employees.remove(&id).is_some() {
            println!("Employee with ID {} removed.", id);
        } else {
            println!("Employee with ID {} not found.", id);
        }
    }

    fn update_employee(&mut self, id: u32, name: Option<String>, department: Option<String>, salary: Option<f64>) {
        if let Some(employee) = self.employees.get_mut(&id) {
            if let Some(name) = name {
                employee.name = name;
            }
            if let Some(department) = department {
                employee.department = department;
            }
            if let Some(salary) = salary {
                employee.salary = salary;
            }
            println!("Employee updated: {:?}", employee);
        } else {
            println!("Employee with ID {} not found.", id);
        }
    }

    fn list_employees(&self) {
        for employee in self.employees.values() {
            println!("{:?}", employee);
        }
    }
}

fn main() {
    let mut manager = EmployeeManager::new();
    
    loop {
        println!("\n--- Employee Management System ---");
        println!("1. Add Employee");
        println!("2. Remove Employee");
        println!("3. Update Employee");
        println!("4. List Employees");
        println!("5. Exit");

        let mut choice = String::new();
        io::stdin().read_line(&mut choice).unwrap();
        let choice = choice.trim();

        match choice {
            "1" => {
                let mut id_str = String::new();
                let mut name = String::new();
                let mut department = String::new();
                let mut salary_str = String::new();

                println!("Enter Employee ID: ");
                io::stdin().read_line(&mut id_str).unwrap();
                let id: u32 = id_str.trim().parse().unwrap();

                println!("Enter Name: ");
                io::stdin().read_line(&mut name).unwrap();

                println!("Enter Department: ");
                io::stdin().read_line(&mut department).unwrap();

                println!("Enter Salary: ");
                io::stdin().read_line(&mut salary_str).unwrap();
                let salary: f64 = salary_str.trim().parse().unwrap();

                let employee = Employee {
                    id,
                    name: name.trim().to_string(),
                    department: department.trim().to_string(),
                    salary,
                };

                manager.add_employee(employee);
                println!("Employee added successfully!");
            }
            "2" => {
                let mut id_str = String::new();
                println!("Enter Employee ID to remove: ");
                io::stdin().read_line(&mut id_str).unwrap();
                let id: u32 = id_str.trim().parse().unwrap();
                manager.remove_employee(id);
            }
            "3" => {
                let mut id_str = String::new();
                println!("Enter Employee ID to update: ");
                io::stdin().read_line(&mut id_str).unwrap();
                let id: u32 = id_str.trim().parse().unwrap();

                let mut name = String::new();
                let mut department = String::new();
                let mut salary_str = String::new();

                println!("Enter new name (leave blank to skip): ");
                io::stdin().read_line(&mut name).unwrap();

                println!("Enter new department (leave blank to skip): ");
                io::stdin().read_line(&mut department).unwrap();

                println!("Enter new salary (leave blank to skip): ");
                io::stdin().read_line(&mut salary_str).unwrap();

                let name_option = if name.trim().is_empty() { None } else { Some(name.trim().to_string()) };
                let department_option = if department.trim().is_empty() { None } else { Some(department.trim().to_string()) };
                let salary_option = if salary_str.trim().is_empty() { None } else { Some(salary_str.trim().parse::<f64>().unwrap()) };

                manager.update_employee(id, name_option, department_option, salary_option);
            }
            "4" => manager.list_employees(),
            "5" => {
                println!("Exiting...");
                break;
            }
            _ => println!("Invalid choice!"),
        }
    }
}
✅ Features:
Add, remove, update, and list employees.

Uses a HashMap for efficient employee lookup.

Supports optional updates for name, department, or salary.

If you want, I can also show a version that saves employees to a JSON file, so your data persists between program runs. That’s often the next step for a real management system.

Do you want me to do that?

You've reached your message limit. Upgrade to ChatGPT Plus or try again in 14 minutes.

Upgrade


Attach

Search

Study

Voice
No file chosenNo file chosen
ChatGPT can make mistakes. Check important info.
