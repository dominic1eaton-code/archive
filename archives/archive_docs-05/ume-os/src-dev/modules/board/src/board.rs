use std::collections::HashMap;

#[derive(Clone, Debug)]
pub struct BoardMember {
    pub id: u32,
    pub name: String,
    pub position: String,
    pub email: String,
}

#[derive(Clone, Debug)]
pub struct Meeting {
    pub id: u32,
    pub title: String,
    pub date: String,
    pub attendees: Vec<u32>,
    pub agenda: String,
}

pub struct CorporateBoard {
    members: HashMap<u32, BoardMember>,
    meetings: HashMap<u32, Meeting>,
    next_member_id: u32,
    next_meeting_id: u32,
}

impl CorporateBoard {
    pub fn new() -> Self {
        Self {
            members: HashMap::new(),
            meetings: HashMap::new(),
            next_member_id: 1,
            next_meeting_id: 1,
        }
    }

    pub fn add_member(&mut self, name: String, position: String, email: String) -> u32 {
        let id = self.next_member_id;
        let member = BoardMember { id, name, position, email };
        self.members.insert(id, member);
        self.next_member_id += 1;
        id
    }

    pub fn remove_member(&mut self, id: u32) -> Option<BoardMember> {
        self.members.remove(&id)
    }

    pub fn get_member(&self, id: u32) -> Option<&BoardMember> {
        self.members.get(&id)
    }

    pub fn list_members(&self) -> Vec<&BoardMember> {
        self.members.values().collect()
    }

    pub fn schedule_meeting(&mut self, title: String, date: String, agenda: String) -> u32 {
        let id = self.next_meeting_id;
        let meeting = Meeting {
            id,
            title,
            date,
            attendees: Vec::new(),
            agenda,
        };
        self.meetings.insert(id, meeting);
        self.next_meeting_id += 1;
        id
    }

    pub fn add_attendee(&mut self, meeting_id: u32, member_id: u32) -> bool {
        if let Some(meeting) = self.meetings.get_mut(&meeting_id) {
            if self.members.contains_key(&member_id) {
                meeting.attendees.push(member_id);
                return true;
            }
        }
        false
    }

    pub fn get_meeting(&self, id: u32) -> Option<&Meeting> {
        self.meetings.get(&id)
    }

    pub fn list_meetings(&self) -> Vec<&Meeting> {
        self.meetings.values().collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_add_member() {
        let mut board = CorporateBoard::new();
        let id = board.add_member("John Doe".to_string(), "CEO".to_string(), "john@corp.com".to_string());
        assert_eq!(id, 1);
        assert!(board.get_member(id).is_some());
    }
}