Skip to content
You said:
create a communications department management system in rust
ChatGPT said:
Absolutely! Let's break this down carefully. We’ll aim for a Communications Department Management System in Rust that could handle employees, messages, and internal announcements. I’ll create a modular, maintainable structure, using Rust structs, enums, and a simple in-memory storage system (without a database for now, but we can extend it later).

Here’s a full example:

use std::collections::HashMap;

// ===== Data Models =====
#[derive(Debug, Clone)]
struct Employee {
    id: u32,
    name: String,
    position: String,
    email: String,
}

#[derive(Debug, Clone)]
struct Message {
    id: u32,
    sender_id: u32,
    receiver_id: u32,
    content: String,
}

#[derive(Debug, Clone)]
struct Announcement {
    id: u32,
    title: String,
    content: String,
}

// ===== Management System =====
struct CommunicationsDepartment {
    employees: HashMap<u32, Employee>,
    messages: HashMap<u32, Message>,
    announcements: HashMap<u32, Announcement>,
    next_employee_id: u32,
    next_message_id: u32,
    next_announcement_id: u32,
}

impl CommunicationsDepartment {
    fn new() -> Self {
        Self {
            employees: HashMap::new(),
            messages: HashMap::new(),
            announcements: HashMap::new(),
            next_employee_id: 1,
            next_message_id: 1,
            next_announcement_id: 1,
        }
    }

    // ===== Employee Management =====
    fn add_employee(&mut self, name: String, position: String, email: String) -> u32 {
        let id = self.next_employee_id;
        self.next_employee_id += 1;

        let employee = Employee { id, name, position, email };
        self.employees.insert(id, employee);
        id
    }

    fn remove_employee(&mut self, id: u32) -> bool {
        self.employees.remove(&id).is_some()
    }

    fn list_employees(&self) {
        println!("Employees:");
        for employee in self.employees.values() {
            println!("{:?}", employee);
        }
    }

    // ===== Message Management =====
    fn send_message(&mut self, sender_id: u32, receiver_id: u32, content: String) -> u32 {
        let id = self.next_message_id;
        self.next_message_id += 1;

        let message = Message { id, sender_id, receiver_id, content };
        self.messages.insert(id, message);
        id
    }

    fn list_messages(&self) {
        println!("Messages:");
        for message in self.messages.values() {
            println!("{:?}", message);
        }
    }

    // ===== Announcement Management =====
    fn add_announcement(&mut self, title: String, content: String) -> u32 {
        let id = self.next_announcement_id;
        self.next_announcement_id += 1;

        let announcement = Announcement { id, title, content };
        self.announcements.insert(id, announcement);
        id
    }

    fn list_announcements(&self) {
        println!("Announcements:");
        for announcement in self.announcements.values() {
            println!("{:?}", announcement);
        }
    }
}

// ===== Main Function =====
fn main() {
    let mut department = CommunicationsDepartment::new();

    // Add employees
    let alice_id = department.add_employee("Alice".to_string(), "Manager".to_string(), "alice@example.com".to_string());
    let bob_id = department.add_employee("Bob".to_string(), "Coordinator".to_string(), "bob@example.com".to_string());

    // Send a message
    department.send_message(alice_id, bob_id, "Hello Bob, please prepare the report.".to_string());

    // Add an announcement
    department.add_announcement("Team Meeting".to_string(), "All employees must attend the team meeting at 10 AM.".to_string());

    // List data
    department.list_employees();
    department.list_messages();
    department.list_announcements();
}
✅ Features in this system:
Employee management: Add, remove, list.

Message management: Send messages between employees, list messages.

Announcements: Add and list announcements.

In-memory storage: Uses HashMap for simplicity, IDs auto-increment.

💡 Possible Extensions:
Persist data using a database (e.g., SQLite with rusqlite).

Add authentication for employees.

Add roles/permissions.

Implement a CLI or web interface using axum or rocket.

If you want, I can rewrite this as a full CLI app where you can type commands like add_employee, send_message, list_announcements, making it interactive.

Do you want me to do that next?

You said:
rewrite this as a full CLI app where you can type commands like add_employee, send_message, list_announcements
ChatGPT said:
Absolutely! Let’s turn your Communications Department Management System into a fully interactive CLI app in Rust. We’ll use std::io for input and a simple command parser.

Here’s a complete example:

use std::collections::HashMap;
use std::io::{self, Write};

// ===== Data Models =====
#[derive(Debug, Clone)]
struct Employee {
    id: u32,
    name: String,
    position: String,
    email: String,
}

#[derive(Debug, Clone)]
struct Message {
    id: u32,
    sender_id: u32,
    receiver_id: u32,
    content: String,
}

#[derive(Debug, Clone)]
struct Announcement {
    id: u32,
    title: String,
    content: String,
}

// ===== Management System =====
struct CommunicationsDepartment {
    employees: HashMap<u32, Employee>,
    messages: HashMap<u32, Message>,
    announcements: HashMap<u32, Announcement>,
    next_employee_id: u32,
    next_message_id: u32,
    next_announcement_id: u32,
}

impl CommunicationsDepartment {
    fn new() -> Self {
        Self {
            employees: HashMap::new(),
            messages: HashMap::new(),
            announcements: HashMap::new(),
            next_employee_id: 1,
            next_message_id: 1,
            next_announcement_id: 1,
        }
    }

    // ===== Employee Management =====
    fn add_employee(&mut self, name: String, position: String, email: String) -> u32 {
        let id = self.next_employee_id;
        self.next_employee_id += 1;

        let employee = Employee { id, name, position, email };
        self.employees.insert(id, employee);
        id
    }

    fn remove_employee(&mut self, id: u32) -> bool {
        self.employees.remove(&id).is_some()
    }

    fn list_employees(&self) {
        println!("Employees:");
        for employee in self.employees.values() {
            println!("{:?}", employee);
        }
    }

    // ===== Message Management =====
    fn send_message(&mut self, sender_id: u32, receiver_id: u32, content: String) -> u32 {
        let id = self.next_message_id;
        self.next_message_id += 1;

        let message = Message { id, sender_id, receiver_id, content };
        self.messages.insert(id, message);
        id
    }

    fn list_messages(&self) {
        println!("Messages:");
        for message in self.messages.values() {
            let sender = &self.employees.get(&message.sender_id).map_or("Unknown".to_string(), |e| e.name.clone());
            let receiver = &self.employees.get(&message.receiver_id).map_or("Unknown".to_string(), |e| e.name.clone());
            println!("From: {} To: {} | {:?}", sender, receiver, message.content);
        }
    }

    // ===== Announcement Management =====
    fn add_announcement(&mut self, title: String, content: String) -> u32 {
        let id = self.next_announcement_id;
        self.next_announcement_id += 1;

        let announcement = Announcement { id, title, content };
        self.announcements.insert(id, announcement);
        id
    }

    fn list_announcements(&self) {
        println!("Announcements:");
        for announcement in self.announcements.values() {
            println!("{}: {}", announcement.title, announcement.content);
        }
    }
}

// ===== CLI Utilities =====
fn input(prompt: &str) -> String {
    print!("{}", prompt);
    io::stdout().flush().unwrap();
    let mut buf = String::new();
    io::stdin().read_line(&mut buf).unwrap();
    buf.trim().to_string()
}

fn main() {
    let mut department = CommunicationsDepartment::new();

    println!("Welcome to the Communications Department Management CLI!");
    println!("Type 'help' to see available commands.\n");

    loop {
        let command = input("> ");

        match command.as_str() {
            "help" => {
                println!("Available commands:");
                println!("add_employee - Add a new employee");
                println!("remove_employee - Remove an employee by ID");
                println!("list_employees - List all employees");
                println!("send_message - Send a message between employees");
                println!("list_messages - List all messages");
                println!("add_announcement - Add a new announcement");
                println!("list_announcements - List all announcements");
                println!("exit - Exit the program");
            }
            "add_employee" => {
                let name = input("Name: ");
                let position = input("Position: ");
                let email = input("Email: ");
                let id = department.add_employee(name, position, email);
                println!("Employee added with ID {}", id);
            }
            "remove_employee" => {
                let id_str = input("Employee ID: ");
                if let Ok(id) = id_str.parse::<u32>() {
                    if department.remove_employee(id) {
                        println!("Employee removed.");
                    } else {
                        println!("Employee not found.");
                    }
                } else {
                    println!("Invalid ID.");
                }
            }
            "list_employees" => {
                department.list_employees();
            }
            "send_message" => {
                let sender_str = input("Sender ID: ");
                let receiver_str = input("Receiver ID: ");
                let content = input("Message: ");
                if let (Ok(sender_id), Ok(receiver_id)) = (sender_str.parse::<u32>(), receiver_str.parse::<u32>()) {
                    if department.employees.contains_key(&sender_id) && department.employees.contains_key(&receiver_id) {
                        let msg_id = department.send_message(sender_id, receiver_id, content);
                        println!("Message sent with ID {}", msg_id);
                    } else {
                        println!("Sender or receiver not found.");
                    }
                } else {
                    println!("Invalid IDs.");
                }
            }
            "list_messages" => {
                department.list_messages();
            }
            "add_announcement" => {
                let title = input("Title: ");
                let content = input("Content: ");
                let id = department.add_announcement(title, content);
                println!("Announcement added with ID {}", id);
            }
            "list_announcements" => {
                department.list_announcements();
            }
            "exit" => break,
            _ => println!("Unknown command. Type 'help' for a list of commands."),
        }
    }

    println!("Goodbye!");
}
✅ Features of this CLI app:
Interactive command-line interface.

Commands for adding/removing/listing employees.

Sending/listing messages between employees.

Adding/listing announcements.

Simple input parsing with error handling.

Example Usage:
> add_employee
Name: Alice
Position: Manager
Email: alice@example.com
Employee added with ID 1

> add_employee
Name: Bob
Position: Coordinator
Email: bob@example.com
Employee added with ID 2

> send_message
Sender ID: 1
Receiver ID: 2
Message: Hello Bob!
Message sent with ID 1

> list_messages
From: Alice To: Bob | "Hello Bob!"
If you want, I can upgrade this CLI to support commands with arguments directly (like add_employee Alice Manager alice@example.com) instead of interactive prompts, which is more convenient for power users.

Do you want me to do that?

You said:
upgrade this CLI to support commands with arguments directly (like add_employee Alice Manager alice@example.com) i
ChatGPT said:
Perfect! Let’s upgrade the CLI so you can run commands with arguments directly, like:

add_employee Alice Manager alice@example.com
send_message 1 2 "Hello Bob!"
We’ll parse the command line input, split by spaces, and handle arguments intelligently. For strings with spaces (like messages or announcement content), the user can wrap them in quotes.

Here’s the upgraded version:

use std::collections::HashMap;
use std::io::{self, Write};

// ===== Data Models =====
#[derive(Debug, Clone)]
struct Employee {
    id: u32,
    name: String,
    position: String,
    email: String,
}

#[derive(Debug, Clone)]
struct Message {
    id: u32,
    sender_id: u32,
    receiver_id: u32,
    content: String,
}

#[derive(Debug, Clone)]
struct Announcement {
    id: u32,
    title: String,
    content: String,
}

// ===== Management System =====
struct CommunicationsDepartment {
    employees: HashMap<u32, Employee>,
    messages: HashMap<u32, Message>,
    announcements: HashMap<u32, Announcement>,
    next_employee_id: u32,
    next_message_id: u32,
    next_announcement_id: u32,
}

impl CommunicationsDepartment {
    fn new() -> Self {
        Self {
            employees: HashMap::new(),
            messages: HashMap::new(),
            announcements: HashMap::new(),
            next_employee_id: 1,
            next_message_id: 1,
            next_announcement_id: 1,
        }
    }

    // ===== Employee Management =====
    fn add_employee(&mut self, name: String, position: String, email: String) -> u32 {
        let id = self.next_employee_id;
        self.next_employee_id += 1;

        let employee = Employee { id, name, position, email };
        self.employees.insert(id, employee);
        id
    }

    fn remove_employee(&mut self, id: u32) -> bool {
        self.employees.remove(&id).is_some()
    }

    fn list_employees(&self) {
        println!("Employees:");
        for employee in self.employees.values() {
            println!("{:?}", employee);
        }
    }

    // ===== Message Management =====
    fn send_message(&mut self, sender_id: u32, receiver_id: u32, content: String) -> u32 {
        let id = self.next_message_id;
        self.next_message_id += 1;

        let message = Message { id, sender_id, receiver_id, content };
        self.messages.insert(id, message);
        id
    }

    fn list_messages(&self) {
        println!("Messages:");
        for message in self.messages.values() {
            let sender = &self.employees.get(&message.sender_id).map_or("Unknown".to_string(), |e| e.name.clone());
            let receiver = &self.employees.get(&message.receiver_id).map_or("Unknown".to_string(), |e| e.name.clone());
            println!("From: {} To: {} | {:?}", sender, receiver, message.content);
        }
    }

    // ===== Announcement Management =====
    fn add_announcement(&mut self, title: String, content: String) -> u32 {
        let id = self.next_announcement_id;
        self.next_announcement_id += 1;

        let announcement = Announcement { id, title, content };
        self.announcements.insert(id, announcement);
        id
    }

    fn list_announcements(&self) {
        println!("Announcements:");
        for announcement in self.announcements.values() {
            println!("{}: {}", announcement.title, announcement.content);
        }
    }
}

// ===== CLI Utilities =====
fn input(prompt: &str) -> String {
    print!("{}", prompt);
    io::stdout().flush().unwrap();
    let mut buf = String::new();
    io::stdin().read_line(&mut buf).unwrap();
    buf.trim().to_string()
}

// Split command line into arguments, respecting quotes
fn parse_command(input: &str) -> Vec<String> {
    let mut args = Vec::new();
    let mut current = String::new();
    let mut in_quotes = false;

    for c in input.chars() {
        match c {
            '"' => {
                in_quotes = !in_quotes;
            }
            ' ' if !in_quotes => {
                if !current.is_empty() {
                    args.push(current.clone());
                    current.clear();
                }
            }
            _ => current.push(c),
        }
    }
    if !current.is_empty() {
        args.push(current);
    }
    args
}

fn main() {
    let mut department = CommunicationsDepartment::new();

    println!("Welcome to the Communications Department Management CLI!");
    println!("Type 'help' to see available commands.\n");

    loop {
        let line = input("> ");
        let args = parse_command(&line);

        if args.is_empty() {
            continue;
        }

        match args[0].as_str() {
            "help" => {
                println!("Available commands:");
                println!("add_employee <name> <position> <email>");
                println!("remove_employee <id>");
                println!("list_employees");
                println!("send_message <sender_id> <receiver_id> <message>");
                println!("list_messages");
                println!("add_announcement <title> <content>");
                println!("list_announcements");
                println!("exit");
            }
            "add_employee" => {
                if args.len() < 4 {
                    println!("Usage: add_employee <name> <position> <email>");
                    continue;
                }
                let name = args[1].clone();
                let position = args[2].clone();
                let email = args[3].clone();
                let id = department.add_employee(name, position, email);
                println!("Employee added with ID {}", id);
            }
            "remove_employee" => {
                if args.len() < 2 {
                    println!("Usage: remove_employee <id>");
                    continue;
                }
                if let Ok(id) = args[1].parse::<u32>() {
                    if department.remove_employee(id) {
                        println!("Employee removed.");
                    } else {
                        println!("Employee not found.");
                    }
                } else {
                    println!("Invalid ID.");
                }
            }
            "list_employees" => department.list_employees(),
            "send_message" => {
                if args.len() < 4 {
                    println!("Usage: send_message <sender_id> <receiver_id> <message>");
                    continue;
                }
                let sender_id = args[1].parse::<u32>();
                let receiver_id = args[2].parse::<u32>();
                if sender_id.is_err() || receiver_id.is_err() {
                    println!("Invalid sender or receiver ID.");
                    continue;
                }
                let sender_id = sender_id.unwrap();
                let receiver_id = receiver_id.unwrap();
                let message = args[3..].join(" ");
                if department.employees.contains_key(&sender_id) && department.employees.contains_key(&receiver_id) {
                    let msg_id = department.send_message(sender_id, receiver_id, message);
                    println!("Message sent with ID {}", msg_id);
                } else {
                    println!("Sender or receiver not found.");
                }
            }
            "list_messages" => department.list_messages(),
            "add_announcement" => {
                if args.len() < 3 {
                    println!("Usage: add_announcement <title> <content>");
                    continue;
                }
                let title = args[1].clone();
                let content = args[2..].join(" ");
                let id = department.add_announcement(title, content);
                println!("Announcement added with ID {}", id);
            }
            "list_announcements" => department.list_announcements(),
            "exit" => break,
            _ => println!("Unknown command. Type 'help' for a list of commands."),
        }
    }

    println!("Goodbye!");
}
✅ Upgrades:
Commands now take arguments directly:

add_employee Alice Manager alice@example.com
send_message 1 2 "Hello Bob!"
add_announcement "Team Meeting" "All employees must attend"
Supports quoted strings for arguments with spaces.

No more interactive prompts for each field—everything can be entered in one line.

If you want, I can also add tab-completion-like suggestions for employee IDs and command names, making this CLI almost like a mini shell for your department.

Do you want me to do that next?

You said:
add tab-completion-like suggestions for employee IDs and command names, making this CLI almost like a mini shell for your department.
ChatGPT said:
Perfect! Let’s make your CLI feel like a mini shell with tab-completion-like suggestions. While Rust doesn’t have native shell completion in std::io, we can simulate it by showing suggestions dynamically as the user types a partial command.

Here’s the plan:

Suggest command names if the input is partial.

Suggest employee IDs when relevant (for send_message or remove_employee).

This will act like “tab-completion” but triggered when user presses Enter and the input is incomplete.

Here’s an upgraded version:

use std::collections::HashMap;
use std::io::{self, Write};

// ===== Data Models =====
#[derive(Debug, Clone)]
struct Employee {
    id: u32,
    name: String,
    position: String,
    email: String,
}

#[derive(Debug, Clone)]
struct Message {
    id: u32,
    sender_id: u32,
    receiver_id: u32,
    content: String,
}

#[derive(Debug, Clone)]
struct Announcement {
    id: u32,
    title: String,
    content: String,
}

// ===== Management System =====
struct CommunicationsDepartment {
    employees: HashMap<u32, Employee>,
    messages: HashMap<u32, Message>,
    announcements: HashMap<u32, Announcement>,
    next_employee_id: u32,
    next_message_id: u32,
    next_announcement_id: u32,
}

impl CommunicationsDepartment {
    fn new() -> Self {
        Self {
            employees: HashMap::new(),
            messages: HashMap::new(),
            announcements: HashMap::new(),
            next_employee_id: 1,
            next_message_id: 1,
            next_announcement_id: 1,
        }
    }

    fn add_employee(&mut self, name: String, position: String, email: String) -> u32 {
        let id = self.next_employee_id;
        self.next_employee_id += 1;
        self.employees.insert(id, Employee { id, name, position, email });
        id
    }

    fn remove_employee(&mut self, id: u32) -> bool {
        self.employees.remove(&id).is_some()
    }

    fn list_employees(&self) {
        println!("Employees:");
        for employee in self.employees.values() {
            println!("{:?}", employee);
        }
    }

    fn send_message(&mut self, sender_id: u32, receiver_id: u32, content: String) -> u32 {
        let id = self.next_message_id;
        self.next_message_id += 1;
        self.messages.insert(id, Message { id, sender_id, receiver_id, content });
        id
    }

    fn list_messages(&self) {
        println!("Messages:");
        for message in self.messages.values() {
            let sender = &self.employees.get(&message.sender_id).map_or("Unknown".to_string(), |e| e.name.clone());
            let receiver = &self.employees.get(&message.receiver_id).map_or("Unknown".to_string(), |e| e.name.clone());
            println!("From: {} To: {} | {:?}", sender, receiver, message.content);
        }
    }

    fn add_announcement(&mut self, title: String, content: String) -> u32 {
        let id = self.next_announcement_id;
        self.next_announcement_id += 1;
        self.announcements.insert(id, Announcement { id, title, content });
        id
    }

    fn list_announcements(&self) {
        println!("Announcements:");
        for announcement in self.announcements.values() {
            println!("{}: {}", announcement.title, announcement.content);
        }
    }

    fn suggest_employee_ids(&self) {
        let ids: Vec<String> = self.employees.keys().map(|id| id.to_string()).collect();
        if !ids.is_empty() {
            println!("Available employee IDs: {}", ids.join(", "));
        }
    }
}

// ===== CLI Utilities =====
fn input(prompt: &str) -> String {
    print!("{}", prompt);
    io::stdout().flush().unwrap();
    let mut buf = String::new();
    io::stdin().read_line(&mut buf).unwrap();
    buf.trim().to_string()
}

// Split command line into arguments, respecting quotes
fn parse_command(input: &str) -> Vec<String> {
    let mut args = Vec::new();
    let mut current = String::new();
    let mut in_quotes = false;

    for c in input.chars() {
        match c {
            '"' => in_quotes = !in_quotes,
            ' ' if !in_quotes => {
                if !current.is_empty() {
                    args.push(current.clone());
                    current.clear();
                }
            }
            _ => current.push(c),
        }
    }
    if !current.is_empty() {
        args.push(current);
    }
    args
}

// Commands list
const COMMANDS: &[&str] = &[
    "help", "add_employee", "remove_employee", "list_employees",
    "send_message", "list_messages", "add_announcement", "list_announcements", "exit"
];

// Suggest commands if input partially matches
fn suggest_command(partial: &str) {
    let suggestions: Vec<&str> = COMMANDS.iter().filter(|cmd| cmd.starts_with(partial)).cloned().collect();
    if !suggestions.is_empty() {
        println!("Did you mean? {}", suggestions.join(", "));
    }
}

fn main() {
    let mut department = CommunicationsDepartment::new();

    println!("Welcome to the Communications Department Management CLI!");
    println!("Type 'help' to see available commands.\n");

    loop {
        let line = input("> ");
        if line.is_empty() {
            continue;
        }

        let args = parse_command(&line);

        if args.is_empty() {
            continue;
        }

        match args[0].as_str() {
            "help" => {
                println!("Available commands:");
                println!("add_employee <name> <position> <email>");
                println!("remove_employee <id>");
                println!("list_employees");
                println!("send_message <sender_id> <receiver_id> <message>");
                println!("list_messages");
                println!("add_announcement <title> <content>");
                println!("list_announcements");
                println!("exit");
            }
            "add_employee" => {
                if args.len() < 4 {
                    println!("Usage: add_employee <name> <position> <email>");
                    continue;
                }
                let id = department.add_employee(args[1].clone(), args[2].clone(), args[3].clone());
                println!("Employee added with ID {}", id);
            }
            "remove_employee" => {
                if args.len() < 2 {
                    println!("Usage: remove_employee <id>");
                    department.suggest_employee_ids();
                    continue;
                }
                if let Ok(id) = args[1].parse::<u32>() {
                    if department.remove_employee(id) {
                        println!("Employee removed.");
                    } else {
                        println!("Employee not found.");
                        department.suggest_employee_ids();
                    }
                } else {
                    println!("Invalid ID.");
                    department.suggest_employee_ids();
                }
            }
            "list_employees" => department.list_employees(),
            "send_message" => {
                if args.len() < 4 {
                    println!("Usage: send_message <sender_id> <receiver_id> <message>");
                    department.suggest_employee_ids();
                    continue;
                }
                let sender_id = args[1].parse::<u32>();
                let receiver_id = args[2].parse::<u32>();
                if sender_id.is_err() || receiver_id.is_err() {
                    println!("Invalid sender or receiver ID.");
                    department.suggest_employee_ids();
                    continue;
                }
                let sender_id = sender_id.unwrap();
                let receiver_id = receiver_id.unwrap();
                let message = args[3..].join(" ");
                if department.employees.contains_key(&sender_id) && department.employees.contains_key(&receiver_id) {
                    let msg_id = department.send_message(sender_id, receiver_id, message);
                    println!("Message sent with ID {}", msg_id);
                } else {
                    println!("Sender or receiver not found.");
                    department.suggest_employee_ids();
                }
            }
            "list_messages" => department.list_messages(),
            "add_announcement" => {
                if args.len() < 3 {
                    println!("Usage: add_announcement <title> <content>");
                    continue;
                }
                let title = args[1].clone();
                let content = args[2..].join(" ");
                let id = department.add_announcement(title, content);
                println!("Announcement added with ID {}", id);
            }
            "list_announcements" => department.list_announcements(),
            "exit" => break,
            cmd => {
                println!("Unknown command: '{}'", cmd);
                suggest_command(cmd);
            }
        }
    }

    println!("Goodbye!");
}
✅ What’s New:
Command suggestions: If the user types an unknown command partially, suggestions are shown.

Employee ID suggestions: If IDs are invalid or missing for send_message and remove_employee, the CLI lists all available employee IDs.

Still supports quoted arguments: Multi-word messages or announcement content work fine.

Mimics tab-completion-like behavior without relying on OS-level readline features.

Example interaction:

> send_mes
Unknown command: 'send_mes'
Did you mean? send_message

> send_message 1 99 "Hello"
Sender or receiver not found.
Available employee IDs: 1, 2, 3
If you want, I can take this one step further and integrate real tab completion using the rustyline crate, so pressing Tab actually auto-completes commands and IDs while typing.

Do you want me to do that next?

You said:
take this one step further and integrate real tab completion using the rustyline crate,
ChatGPT said:
Perfect! Integrating real tab completion in Rust is best done with the rustyline crate, which provides readline-like functionality with auto-completion. We can make a fully interactive shell where pressing Tab completes commands and employee IDs.

Here’s a step-by-step implementation:

1️⃣ Add dependencies in Cargo.toml:
[dependencies]
rustyline = "11.1.0"
2️⃣ Complete CLI with Tab Completion:
use rustyline::completion::{Completer, Pair};
use rustyline::error::ReadlineError;
use rustyline::{Editor, Context};
use std::collections::HashMap;
use std::sync::Arc;

// ===== Data Models =====
#[derive(Debug, Clone)]
struct Employee {
    id: u32,
    name: String,
    position: String,
    email: String,
}

#[derive(Debug, Clone)]
struct Message {
    id: u32,
    sender_id: u32,
    receiver_id: u32,
    content: String,
}

#[derive(Debug, Clone)]
struct Announcement {
    id: u32,
    title: String,
    content: String,
}

// ===== Management System =====
struct CommunicationsDepartment {
    employees: HashMap<u32, Employee>,
    messages: HashMap<u32, Message>,
    announcements: HashMap<u32, Announcement>,
    next_employee_id: u32,
    next_message_id: u32,
    next_announcement_id: u32,
}

impl CommunicationsDepartment {
    fn new() -> Self {
        Self {
            employees: HashMap::new(),
            messages: HashMap::new(),
            announcements: HashMap::new(),
            next_employee_id: 1,
            next_message_id: 1,
            next_announcement_id: 1,
        }
    }

    fn add_employee(&mut self, name: String, position: String, email: String) -> u32 {
        let id = self.next_employee_id;
        self.next_employee_id += 1;
        self.employees.insert(id, Employee { id, name, position, email });
        id
    }

    fn remove_employee(&mut self, id: u32) -> bool {
        self.employees.remove(&id).is_some()
    }

    fn list_employees(&self) {
        println!("Employees:");
        for employee in self.employees.values() {
            println!("{:?}", employee);
        }
    }

    fn send_message(&mut self, sender_id: u32, receiver_id: u32, content: String) -> u32 {
        let id = self.next_message_id;
        self.next_message_id += 1;
        self.messages.insert(id, Message { id, sender_id, receiver_id, content });
        id
    }

    fn list_messages(&self) {
        println!("Messages:");
        for message in self.messages.values() {
            let sender = &self.employees.get(&message.sender_id).map_or("Unknown".to_string(), |e| e.name.clone());
            let receiver = &self.employees.get(&message.receiver_id).map_or("Unknown".to_string(), |e| e.name.clone());
            println!("From: {} To: {} | {:?}", sender, receiver, message.content);
        }
    }

    fn add_announcement(&mut self, title: String, content: String) -> u32 {
        let id = self.next_announcement_id;
        self.next_announcement_id += 1;
        self.announcements.insert(id, Announcement { id, title, content });
        id
    }

    fn list_announcements(&self) {
        println!("Announcements:");
        for announcement in self.announcements.values() {
            println!("{}: {}", announcement.title, announcement.content);
        }
    }
}

// ===== CLI Completer =====
struct DepartmentCompleter {
    commands: Vec<String>,
    department: Arc<CommunicationsDepartment>,
}

impl Completer for DepartmentCompleter {
    type Candidate = Pair;

    fn complete(&self, line: &str, _pos: usize, _ctx: &Context<'_>) -> Result<Vec<Pair>, ReadlineError> {
        let parts: Vec<&str> = line.split_whitespace().collect();
        let mut matches = Vec::new();

        if parts.is_empty() {
            // suggest all commands
            for cmd in &self.commands {
                matches.push(Pair { display: cmd.clone(), replacement: cmd.clone() });
            }
        } else if parts.len() == 1 {
            // suggest command names
            for cmd in &self.commands {
                if cmd.starts_with(parts[0]) {
                    matches.push(Pair { display: cmd.clone(), replacement: cmd.clone() });
                }
            }
        } else {
            // suggest employee IDs for commands that take IDs
            let cmd = parts[0];
            if ["remove_employee", "send_message"].contains(&cmd) {
                let ids: Vec<String> = self.department.employees.keys().map(|id| id.to_string()).collect();
                for id in ids {
                    if id.starts_with(parts.last().unwrap()) {
                        matches.push(Pair { display: id.clone(), replacement: id.clone() });
                    }
                }
            }
        }
        Ok(matches)
    }
}

// ===== Utility Functions =====
fn parse_command(input: &str) -> Vec<String> {
    let mut args = Vec::new();
    let mut current = String::new();
    let mut in_quotes = false;

    for c in input.chars() {
        match c {
            '"' => in_quotes = !in_quotes,
            ' ' if !in_quotes => {
                if !current.is_empty() {
                    args.push(current.clone());
                    current.clear();
                }
            }
            _ => current.push(c),
        }
    }
    if !current.is_empty() {
        args.push(current);
    }
    args
}

// ===== Main CLI =====
fn main() {
    let mut department = CommunicationsDepartment::new();
    let department_arc = Arc::new(department);

    let commands = vec![
        "help", "add_employee", "remove_employee", "list_employees",
        "send_message", "list_messages", "add_announcement", "list_announcements", "exit"
    ].iter().map(|s| s.to_string()).collect();

    let completer = DepartmentCompleter {
        commands,
        department: Arc::clone(&department_arc),
    };

    let mut rl = Editor::new().unwrap();
    rl.set_completer(Some(completer));

    println!("Communications Department CLI with Tab Completion!");
    println!("Type 'help' to see available commands.");

    loop {
        let readline = rl.readline("> ");
        match readline {
            Ok(line) => {
                let args = parse_command(&line);
                if args.is_empty() { continue; }

                match args[0].as_str() {
                    "help" => {
                        println!("Available commands:");
                        println!("add_employee <name> <position> <email>");
                        println!("remove_employee <id>");
                        println!("list_employees");
                        println!("send_message <sender_id> <receiver_id> <message>");
                        println!("list_messages");
                        println!("add_announcement <title> <content>");
                        println!("list_announcements");
                        println!("exit");
                    }
                    "add_employee" => {
                        if args.len() < 4 { println!("Usage: add_employee <name> <position> <email>"); continue; }
                        let id = Arc::get_mut(&mut Arc::clone(&department_arc)).unwrap()
                            .add_employee(args[1].clone(), args[2].clone(), args[3].clone());
                        println!("Employee added with ID {}", id);
                    }
                    "remove_employee" => {
                        if args.len() < 2 { println!("Usage: remove_employee <id>"); continue; }
                        let id = args[1].parse::<u32>();
                        if let Ok(id) = id {
                            let removed = Arc::get_mut(&mut Arc::clone(&department_arc)).unwrap().remove_employee(id);
                            println!("{}", if removed { "Employee removed." } else { "Employee not found." });
                        } else { println!("Invalid ID."); }
                    }
                    "list_employees" => Arc::clone(&department_arc).list_employees(),
                    "send_message" => {
                        if args.len() < 4 { println!("Usage: send_message <sender_id> <receiver_id> <message>"); continue; }



Attach

Search

Study

No file chosenNo file chosen
ChatGPT can make mistakes. Check important info.
ChatGPT is still generating a response...