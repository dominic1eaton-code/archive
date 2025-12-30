Skip to content
You said:
create an event management system in rust
ChatGPT said:
Sure! I can help you create a basic event management system in Rust. We'll build a simple command-line application that can:

Add events

List events

Search events by name

We’ll use structs, enums, and vectors to store events. Later, we could extend it to use a database or save to a file.

Here’s a working example:

use std::io;
use std::collections::HashMap;

#[derive(Debug, Clone)]
struct Event {
    id: u32,
    name: String,
    date: String,
    location: String,
}

struct EventManager {
    events: HashMap<u32, Event>,
    next_id: u32,
}

impl EventManager {
    fn new() -> Self {
        EventManager {
            events: HashMap::new(),
            next_id: 1,
        }
    }

    fn add_event(&mut self, name: String, date: String, location: String) {
        let event = Event {
            id: self.next_id,
            name,
            date,
            location,
        };
        self.events.insert(self.next_id, event);
        println!("Event added with ID {}", self.next_id);
        self.next_id += 1;
    }

    fn list_events(&self) {
        if self.events.is_empty() {
            println!("No events available.");
            return;
        }

        println!("Listing all events:");
        for event in self.events.values() {
            println!(
                "ID: {}, Name: {}, Date: {}, Location: {}",
                event.id, event.name, event.date, event.location
            );
        }
    }

    fn search_event(&self, keyword: &str) {
        let results: Vec<&Event> = self
            .events
            .values()
            .filter(|e| e.name.to_lowercase().contains(&keyword.to_lowercase()))
            .collect();

        if results.is_empty() {
            println!("No events found with '{}'", keyword);
        } else {
            println!("Search results:");
            for event in results {
                println!(
                    "ID: {}, Name: {}, Date: {}, Location: {}",
                    event.id, event.name, event.date, event.location
                );
            }
        }
    }
}

fn main() {
    let mut event_manager = EventManager::new();
    loop {
        println!("\nEvent Management System");
        println!("1. Add Event");
        println!("2. List Events");
        println!("3. Search Event");
        println!("4. Exit");

        let mut choice = String::new();
        io::stdin().read_line(&mut choice).unwrap();
        let choice = choice.trim();

        match choice {
            "1" => {
                let mut name = String::new();
                let mut date = String::new();
                let mut location = String::new();

                println!("Enter event name:");
                io::stdin().read_line(&mut name).unwrap();
                println!("Enter event date (YYYY-MM-DD):");
                io::stdin().read_line(&mut date).unwrap();
                println!("Enter event location:");
                io::stdin().read_line(&mut location).unwrap();

                event_manager.add_event(
                    name.trim().to_string(),
                    date.trim().to_string(),
                    location.trim().to_string(),
                );
            }
            "2" => event_manager.list_events(),
            "3" => {
                let mut keyword = String::new();
                println!("Enter keyword to search:");
                io::stdin().read_line(&mut keyword).unwrap();
                event_manager.search_event(keyword.trim());
            }
            "4" => {
                println!("Exiting...");
                break;
            }
            _ => println!("Invalid choice!"),
        }
    }
}
✅ Features of this system:
Add events with name, date, and location.

List all events.

Search events by keyword (case-insensitive).

Auto-incrementing id for each event.

If you want, I can also upgrade this system to store events in a JSON file, so data persists between runs. This makes it closer to a real-world event management system.

Do you want me to do that?



Attach

Search

Study

Voice
No file chosenNo file chosen
ChatGPT can make mistakes. Check important info.
