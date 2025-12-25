#[derive(Debug)]
struct Teacher {
    id: u32,
    name: String,
    subject: String,
}

struct TeacherManagementSystem {
    teachers: Vec<Teacher>,
}

impl TeacherManagementSystem {
    fn new() -> Self {
        TeacherManagementSystem {
            teachers: Vec::new(),
        }
    }

    fn add_teacher(&mut self, id: u32, name: String, subject: String) {
        let teacher = Teacher { id, name, subject };
        self.teachers.push(teacher);
    }

    fn list_teachers(&self) {
        for teacher in &self.teachers {
            println!("{:?}", teacher);
        }
    }
}

fn main() {
    let mut tms = TeacherManagementSystem::new();
    tms.add_teacher(1, String::from("Alice"), String::from("Math"));
    tms.add_teacher(2, String::from("Bob"), String::from("Science"));

    println!("List of Teachers:");
    tms.list_teachers();
}