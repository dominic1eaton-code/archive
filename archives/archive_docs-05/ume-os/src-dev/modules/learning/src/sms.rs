use std::collections::HashMap;

#[derive(Debug)]
struct Student {
    id: u32,
    name: String,
    age: u32,
}

struct StudentManagementSystem {
    students: HashMap<u32, Student>,
}

impl StudentManagementSystem {
    fn new() -> Self {
        StudentManagementSystem {
            students: HashMap::new(),
        }
    }

    fn add_student(&mut self, id: u32, name: String, age: u32) {
        let student = Student { id, name, age };
        self.students.insert(id, student);
    }

    fn get_student(&self, id: u32) -> Option<&Student> {
        self.students.get(&id)
    }

    fn remove_student(&mut self, id: u32) {
        self.students.remove(&id);
    }
}

fn main() {
    let mut sms = StudentManagementSystem::new();
    
    sms.add_student(1, String::from("Alice"), 20);
    sms.add_student(2, String::from("Bob"), 22);

    if let Some(student) = sms.get_student(1) {
        println!("Found student: {:?}", student);
    }

    sms.remove_student(1);
    println!("Student with ID 1 removed.");
}