Skip to content
You said:
create an HRM system in rust
ChatGPT said:
Absolutely! Let’s design a simple Human Resource Management (HRM) system in Rust. We'll focus on a console-based application that can:

Add employees

List employees

Update employee information

Remove employees

We’ll use Rust structs, enums, and Vec to manage data. Later, you could expand it to use a database or JSON storage.

Here’s a basic working example:

use std::io;

#[derive(Debug, Clone)]
struct Employee {
    id: u32,
    name: String,
    position: String,
    salary: f64,
}

struct HRMSystem {
    employees: Vec<Employee>,
}

impl HRMSystem {
    fn new() -> Self {
        HRMSystem {
            employees: Vec::new(),
        }
    }

    fn add_employee(&mut self, employee: Employee) {
        self.employees.push(employee);
        println!("Employee added successfully!");
    }

    fn list_employees(&self) {
        if self.employees.is_empty() {
            println!("No employees found.");
            return;
        }

        for emp in &self.employees {
            println!(
                "ID: {}, Name: {}, Position: {}, Salary: ${}",
                emp.id, emp.name, emp.position, emp.salary
            );
        }
    }

    fn remove_employee(&mut self, id: u32) {
        if let Some(pos) = self.employees.iter().position(|e| e.id == id) {
            self.employees.remove(pos);
            println!("Employee removed successfully.");
        } else {
            println!("Employee with ID {} not found.", id);
        }
    }

    fn update_employee(&mut self, id: u32, name: Option<String>, position: Option<String>, salary: Option<f64>) {
        if let Some(emp) = self.employees.iter_mut().find(|e| e.id == id) {
            if let Some(n) = name {
                emp.name = n;
            }
            if let Some(p) = position {
                emp.position = p;
            }
            if let Some(s) = salary {
                emp.salary = s;
            }
            println!("Employee updated successfully.");
        } else {
            println!("Employee with ID {} not found.", id);
        }
    }
}

fn main() {
    let mut system = HRMSystem::new();

    loop {
        println!("\n--- HRM System ---");
        println!("1. Add Employee");
        println!("2. List Employees");
        println!("3. Update Employee");
        println!("4. Remove Employee");
        println!("5. Exit");

        let mut choice = String::new();
        io::stdin().read_line(&mut choice).unwrap();
        let choice = choice.trim();

        match choice {
            "1" => {
                let mut id_str = String::new();
                let mut name = String::new();
                let mut position = String::new();
                let mut salary_str = String::new();

                println!("Enter Employee ID: ");
                io::stdin().read_line(&mut id_str).unwrap();
                let id: u32 = id_str.trim().parse().unwrap_or(0);

                println!("Enter Name: ");
                io::stdin().read_line(&mut name).unwrap();

                println!("Enter Position: ");
                io::stdin().read_line(&mut position).unwrap();

                println!("Enter Salary: ");
                io::stdin().read_line(&mut salary_str).unwrap();
                let salary: f64 = salary_str.trim().parse().unwrap_or(0.0);

                let employee = Employee {
                    id,
                    name: name.trim().to_string(),
                    position: position.trim().to_string(),
                    salary,
                };

                system.add_employee(employee);
            }
            "2" => system.list_employees(),
            "3" => {
                let mut id_str = String::new();
                println!("Enter Employee ID to update: ");
                io::stdin().read_line(&mut id_str).unwrap();
                let id: u32 = id_str.trim().parse().unwrap_or(0);

                let mut name = String::new();
                let mut position = String::new();
                let mut salary_str = String::new();

                println!("Enter new name (or leave empty): ");
                io::stdin().read_line(&mut name).unwrap();
                let name = if name.trim().is_empty() { None } else { Some(name.trim().to_string()) };

                println!("Enter new position (or leave empty): ");
                io::stdin().read_line(&mut position).unwrap();
                let position = if position.trim().is_empty() { None } else { Some(position.trim().to_string()) };

                println!("Enter new salary (or leave empty): ");
                io::stdin().read_line(&mut salary_str).unwrap();
                let salary = if salary_str.trim().is_empty() { None } else { Some(salary_str.trim().parse().unwrap_or(0.0)) };

                system.update_employee(id, name, position, salary);
            }
            "4" => {
                let mut id_str = String::new();
                println!("Enter Employee ID to remove: ");
                io::stdin().read_line(&mut id_str).unwrap();
                let id: u32 = id_str.trim().parse().unwrap_or(0);

                system.remove_employee(id);
            }
            "5" => break,
            _ => println!("Invalid option. Try again."),
        }
    }
}
✅ Features:
Add, list, update, remove employees

Basic input validation

Uses Rust's structs and Vec for storage

💡 Next Steps / Improvements:
Persist data in a JSON or SQLite database.

Add department management or roles.

Include search functionality.

Replace console input with a web API using actix-web or rocket.

If you want, I can make a version with JSON persistence, so employees are saved across runs. That would make it more practical than just an in-memory system.

Do you want me to do that next?



Attach

Search

Study

Voice
No file chosenNo file chosen
ChatGPT can make mistakes. Check important info.
