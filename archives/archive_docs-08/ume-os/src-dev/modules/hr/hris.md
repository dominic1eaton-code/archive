Skip to content
You said:
create an HR information system in rust
ChatGPT said:
Absolutely! Let's go step by step. I can help you design a basic HR Information System (HRIS) in Rust, including employee management, departments, and simple CRUD operations. We'll use Rust with SQLite as the database (via rusqlite) for simplicity.

Here’s a full example:

1️⃣ Setup the Project
cargo new hris_rust
cd hris_rust
cargo add rusqlite
cargo add chrono
We use:

rusqlite for database access.

chrono for handling dates (like employee joining date).

2️⃣ Define the Database Schema
Create hris.db or let Rust create it on first run. We'll have two tables:

employees

departments

-- employees table
CREATE TABLE IF NOT EXISTS employees (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    name TEXT NOT NULL,
    email TEXT NOT NULL UNIQUE,
    department_id INTEGER,
    joining_date TEXT NOT NULL,
    FOREIGN KEY(department_id) REFERENCES departments(id)
);

-- departments table
CREATE TABLE IF NOT EXISTS departments (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    name TEXT NOT NULL UNIQUE
);
3️⃣ Rust Code for HRIS
use rusqlite::{params, Connection, Result};
use chrono::NaiveDate;

#[derive(Debug)]
struct Employee {
    id: i32,
    name: String,
    email: String,
    department_id: Option<i32>,
    joining_date: NaiveDate,
}

#[derive(Debug)]
struct Department {
    id: i32,
    name: String,
}

fn main() -> Result<()> {
    let conn = Connection::open("hris.db")?;

    // Create tables
    conn.execute(
        "CREATE TABLE IF NOT EXISTS departments (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            name TEXT NOT NULL UNIQUE
        )",
        [],
    )?;

    conn.execute(
        "CREATE TABLE IF NOT EXISTS employees (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            name TEXT NOT NULL,
            email TEXT NOT NULL UNIQUE,
            department_id INTEGER,
            joining_date TEXT NOT NULL,
            FOREIGN KEY(department_id) REFERENCES departments(id)
        )",
        [],
    )?;

    // Example usage
    add_department(&conn, "Engineering")?;
    add_department(&conn, "HR")?;

    let dept_id = get_department_id(&conn, "Engineering")?;
    add_employee(&conn, "Alice", "alice@example.com", dept_id, "2025-01-01")?;

    let employees = get_all_employees(&conn)?;
    for emp in employees {
        println!("{:?}", emp);
    }

    Ok(())
}

fn add_department(conn: &Connection, name: &str) -> Result<()> {
    conn.execute("INSERT OR IGNORE INTO departments (name) VALUES (?1)", [name])?;
    Ok(())
}

fn get_department_id(conn: &Connection, name: &str) -> Result<Option<i32>> {
    conn.query_row("SELECT id FROM departments WHERE name=?1", [name], |row| row.get(0))
        .optional()
}

fn add_employee(conn: &Connection, name: &str, email: &str, department_id: Option<i32>, joining_date: &str) -> Result<()> {
    conn.execute(
        "INSERT INTO employees (name, email, department_id, joining_date) VALUES (?1, ?2, ?3, ?4)",
        params![name, email, department_id, joining_date],
    )?;
    Ok(())
}

fn get_all_employees(conn: &Connection) -> Result<Vec<Employee>> {
    let mut stmt = conn.prepare("SELECT id, name, email, department_id, joining_date FROM employees")?;
    let employee_iter = stmt.query_map([], |row| {
        Ok(Employee {
            id: row.get(0)?,
            name: row.get(1)?,
            email: row.get(2)?,
            department_id: row.get(3)?,
            joining_date: row.get::<_, String>(4)?.parse().unwrap(),
        })
    })?;

    let mut employees = Vec::new();
    for emp in employee_iter {
        employees.push(emp?);
    }
    Ok(employees)
}
✅ Features Implemented:
Add departments.

Add employees.

List all employees.

Database stored in SQLite.

Uses chrono for date parsing.

4️⃣ Next Steps / Extensions:
Implement update/delete employees and departments.

Add search functionality (by department, joining date, etc.).

Build a CLI menu or integrate with a web framework like actix-web for a REST API.

Implement role-based access control for HR vs regular employees.

If you want, I can extend this example to a full CLI-based HRIS with menu-driven options for all CRUD operations. It would feel more like a real application.

Do you want me to do that next?




Attach

Search

Study

Voice
No file chosenNo file chosen
ChatGPT can make mistakes. Check important info.
