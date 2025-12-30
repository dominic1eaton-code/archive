use std::collections::HashMap;

// ems.rs


#[derive(Debug)]
pub struct Event {
    pub id: u32,
    pub name: String,
    pub description: String,
}

pub struct EventManager {
    events: HashMap<u32, Event>,
    next_id: u32,
}

impl EventManager {
    pub fn new() -> Self {
        EventManager {
            events: HashMap::new(),
            next_id: 1,
        }
    }

    pub fn create_event(&mut self, name: String, description: String) -> u32 {
        let event = Event {
            id: self.next_id,
            name,
            description,
        };
        self.events.insert(self.next_id, event);
        self.next_id += 1;
        self.next_id - 1
    }

    pub fn get_event(&self, id: u32) -> Option<&Event> {
        self.events.get(&id)
    }

    pub fn delete_event(&mut self, id: u32) -> bool {
        self.events.remove(&id).is_some()
    }

    pub fn list_events(&self) -> Vec<&Event> {
        self.events.values().collect()
    }
}