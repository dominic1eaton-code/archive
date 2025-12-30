use std::collections::HashMap;

#[derive(Debug, Clone)]
pub struct Employee {
    pub id: u32,
    pub name: String,
    pub position: String,
    pub email: String,
}

#[derive(Debug, Clone)]
pub struct Room {
    pub id: u32,
    pub name: String,
    pub capacity: u32,
    pub is_available: bool,
}

#[derive(Debug, Clone)]
pub struct Meeting {
    pub id: u32,
    pub title: String,
    pub room_id: u32,
    pub attendees: Vec<u32>,
    pub time: String,
}

pub struct OfficeManager {
    employees: HashMap<u32, Employee>,
    rooms: HashMap<u32, Room>,
    meetings: HashMap<u32, Meeting>,
    next_id: u32,
}

impl OfficeManager {
    pub fn new() -> Self {
        OfficeManager {
            employees: HashMap::new(),
            rooms: HashMap::new(),
            meetings: HashMap::new(),
            next_id: 1,
        }
    }

    pub fn add_employee(&mut self, name: String, position: String, email: String) -> u32 {
        let id = self.next_id;
        self.next_id += 1;
        self.employees.insert(id, Employee { id, name, position, email });
        id
    }

    pub fn add_room(&mut self, name: String, capacity: u32) -> u32 {
        let id = self.next_id;
        self.next_id += 1;
        self.rooms.insert(id, Room { id, name, capacity, is_available: true });
        id
    }

    pub fn schedule_meeting(&mut self, title: String, room_id: u32, attendees: Vec<u32>, time: String) -> Option<u32> {
        if self.rooms.get(&room_id)?.is_available {
            let id = self.next_id;
            self.next_id += 1;
            self.meetings.insert(id, Meeting { id, title, room_id, attendees, time });
            if let Some(room) = self.rooms.get_mut(&room_id) {
                room.is_available = false;
            }
            Some(id)
        } else {
            None
        }
    }

    pub fn get_employee(&self, id: u32) -> Option<&Employee> {
        self.employees.get(&id)
    }

    pub fn get_room(&self, id: u32) -> Option<&Room> {
        self.rooms.get(&id)
    }

    pub fn list_employees(&self) -> Vec<&Employee> {
        self.employees.values().collect()
    }

    pub fn list_available_rooms(&self) -> Vec<&Room> {
        self.rooms.values().filter(|r| r.is_available).collect()
    }
}