// mdm.rs

struct MasterData {
    id: u32,
    name: String,
    description: String,
}

impl MasterData {
    fn new(id: u32, name: &str, description: &str) -> Self {
        MasterData {
            id,
            name: name.to_string(),
            description: description.to_string(),
        }
    }

    fn display(&self) {
        println!("ID: {}, Name: {}, Description: {}", self.id, self.name, self.description);
    }
}

fn main() {
    let data = MasterData::new(1, "Sample Data", "This is a sample master data entry.");
    data.display();
}