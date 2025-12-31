// src/lms.rs

struct Course {
    id: u32,
    title: String,
    description: String,
}

struct User {
    id: u32,
    name: String,
    email: String,
}

struct Enrollment {
    user_id: u32,
    course_id: u32,
}

struct LMS {
    courses: Vec<Course>,
    users: Vec<User>,
    enrollments: Vec<Enrollment>,
}

impl LMS {
    fn new() -> Self {
        LMS {
            courses: Vec::new(),
            users: Vec::new(),
            enrollments: Vec::new(),
        }
    }

    fn add_course(&mut self, title: String, description: String) {
        let id = self.courses.len() as u32 + 1;
        self.courses.push(Course { id, title, description });
    }

    fn add_user(&mut self, name: String, email: String) {
        let id = self.users.len() as u32 + 1;
        self.users.push(User { id, name, email });
    }

    fn enroll_user(&mut self, user_id: u32, course_id: u32) {
        self.enrollments.push(Enrollment { user_id, course_id });
    }
}

fn main() {
    let mut lms = LMS::new();
    lms.add_course("Rust Programming".to_string(), "Learn the basics of Rust.".to_string());
    lms.add_user("Alice".to_string(), "alice@example.com".to_string());
    lms.enroll_user(1, 1);

    println!("LMS initialized with {} courses and {} users.", lms.courses.len(), lms.users.len());
}