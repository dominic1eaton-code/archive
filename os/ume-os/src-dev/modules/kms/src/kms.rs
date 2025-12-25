// kms.rs

struct Knowledge {
    title: String,
    content: String,
}

struct KnowledgeBase {
    entries: Vec<Knowledge>,
}

impl KnowledgeBase {
    fn new() -> Self {
        KnowledgeBase {
            entries: Vec::new(),
        }
    }

    fn add_entry(&mut self, title: String, content: String) {
        let entry = Knowledge { title, content };
        self.entries.push(entry);
    }

    fn get_entry(&self, title: &str) -> Option<&Knowledge> {
        self.entries.iter().find(|entry| entry.title == title)
    }

    fn list_entries(&self) {
        for entry in &self.entries {
            println!("Title: {}", entry.title);
        }
    }
}

fn main() {
    let mut kb = KnowledgeBase::new();
    kb.add_entry("Rust Basics".to_string(), "Learn the basics of Rust programming.".to_string());
    kb.list_entries();

    if let Some(entry) = kb.get_entry("Rust Basics") {
        println!("Found entry: {}", entry.content);
    }
}