use std::collections::HashMap;

// wms.rs


#[derive(Debug)]
struct WikiPage {
    title: String,
    content: String,
}

struct WikiManagementSystem {
    pages: HashMap<String, WikiPage>,
}

impl WikiManagementSystem {
    fn new() -> Self {
        WikiManagementSystem {
            pages: HashMap::new(),
        }
    }

    fn create_page(&mut self, title: &str, content: &str) {
        let page = WikiPage {
            title: title.to_string(),
            content: content.to_string(),
        };
        self.pages.insert(title.to_string(), page);
    }

    fn read_page(&self, title: &str) -> Option<&WikiPage> {
        self.pages.get(title)
    }

    fn update_page(&mut self, title: &str, content: &str) {
        if let Some(page) = self.pages.get_mut(title) {
            page.content = content.to_string();
        }
    }

    fn delete_page(&mut self, title: &str) {
        self.pages.remove(title);
    }
}

fn main() {
    let mut wms = WikiManagementSystem::new();
    
    wms.create_page("Rust", "Rust is a systems programming language.");
    if let Some(page) = wms.read_page("Rust") {
        println!("Page: {:?}", page);
    }
    
    wms.update_page("Rust", "Rust is a systems programming language focused on safety.");
    if let Some(page) = wms.read_page("Rust") {
        println!("Updated Page: {:?}", page);
    }
    
    wms.delete_page("Rust");
    println!("Page after deletion: {:?}", wms.read_page("Rust"));
}