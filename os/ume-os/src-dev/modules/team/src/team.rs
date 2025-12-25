use std::collections::HashMap;

// team.rs


#[derive(Debug)]
struct Member {
    id: u32,
    name: String,
    role: String,
}

struct Team {
    members: HashMap<u32, Member>,
}

impl Team {
    fn new() -> Self {
        Team {
            members: HashMap::new(),
        }
    }

    fn add_member(&mut self, id: u32, name: String, role: String) {
        let member = Member { id, name, role };
        self.members.insert(id, member);
    }

    fn remove_member(&mut self, id: u32) {
        self.members.remove(&id);
    }

    fn list_members(&self) {
        for member in self.members.values() {
            println!("{:?}", member);
        }
    }
}

fn main() {
    let mut team = Team::new();
    team.add_member(1, String::from("Alice"), String::from("Developer"));
    team.add_member(2, String::from("Bob"), String::from("Manager"));

    println!("Team Members:");
    team.list_members();

    team.remove_member(1);
    println!("After removing Alice:");
    team.list_members();
}