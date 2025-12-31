Skip to content
You said:
create a board management system in rust
ChatGPT said:
Sure! Let's build a basic board management system in Rust. By "board management system," I’ll assume you mean something like a task board, similar to a Kanban board, with boards, lists, and tasks. I’ll give a simple CLI-based implementation to start.

Here’s a complete Rust example:

use std::collections::HashMap;
use std::io::{self, Write};

#[derive(Debug)]
struct Task {
    id: u32,
    title: String,
    description: String,
}

#[derive(Debug)]
struct List {
    id: u32,
    name: String,
    tasks: HashMap<u32, Task>,
}

#[derive(Debug)]
struct Board {
    id: u32,
    name: String,
    lists: HashMap<u32, List>,
}

struct BoardManager {
    boards: HashMap<u32, Board>,
    next_board_id: u32,
    next_list_id: u32,
    next_task_id: u32,
}

impl BoardManager {
    fn new() -> Self {
        BoardManager {
            boards: HashMap::new(),
            next_board_id: 1,
            next_list_id: 1,
            next_task_id: 1,
        }
    }

    fn create_board(&mut self, name: &str) {
        let board = Board {
            id: self.next_board_id,
            name: name.to_string(),
            lists: HashMap::new(),
        };
        self.boards.insert(self.next_board_id, board);
        println!("Board created with id {}", self.next_board_id);
        self.next_board_id += 1;
    }

    fn create_list(&mut self, board_id: u32, name: &str) {
        if let Some(board) = self.boards.get_mut(&board_id) {
            let list = List {
                id: self.next_list_id,
                name: name.to_string(),
                tasks: HashMap::new(),
            };
            board.lists.insert(self.next_list_id, list);
            println!("List created with id {}", self.next_list_id);
            self.next_list_id += 1;
        } else {
            println!("Board not found");
        }
    }

    fn create_task(&mut self, board_id: u32, list_id: u32, title: &str, description: &str) {
        if let Some(board) = self.boards.get_mut(&board_id) {
            if let Some(list) = board.lists.get_mut(&list_id) {
                let task = Task {
                    id: self.next_task_id,
                    title: title.to_string(),
                    description: description.to_string(),
                };
                list.tasks.insert(self.next_task_id, task);
                println!("Task created with id {}", self.next_task_id);
                self.next_task_id += 1;
            } else {
                println!("List not found");
            }
        } else {
            println!("Board not found");
        }
    }

    fn show_board(&self, board_id: u32) {
        if let Some(board) = self.boards.get(&board_id) {
            println!("Board {}: {}", board.id, board.name);
            for list in board.lists.values() {
                println!("  List {}: {}", list.id, list.name);
                for task in list.tasks.values() {
                    println!("    Task {}: {} - {}", task.id, task.title, task.description);
                }
            }
        } else {
            println!("Board not found");
        }
    }
}

fn main() {
    let mut manager = BoardManager::new();

    loop {
        print!("> ");
        io::stdout().flush().unwrap();
        let mut input = String::new();
        io::stdin().read_line(&mut input).unwrap();
        let args: Vec<&str> = input.trim().split_whitespace().collect();

        match args.as_slice() {
            ["create_board", name] => manager.create_board(name),
            ["create_list", board_id, name] => {
                if let Ok(board_id) = board_id.parse() {
                    manager.create_list(board_id, name);
                } else {
                    println!("Invalid board id");
                }
            }
            ["create_task", board_id, list_id, title, description] => {
                if let (Ok(board_id), Ok(list_id)) = (board_id.parse(), list_id.parse()) {
                    manager.create_task(board_id, list_id, title, description);
                } else {
                    println!("Invalid board or list id");
                }
            }
            ["show_board", board_id] => {
                if let Ok(board_id) = board_id.parse() {
                    manager.show_board(board_id);
                } else {
                    println!("Invalid board id");
                }
            }
            ["exit"] => break,
            _ => println!("Unknown command"),
        }
    }
}
✅ Features:
Create boards, lists, and tasks.

View a board with its lists and tasks.

CLI interface with simple commands:

create_board MyBoard
create_list 1 Todo
create_task 1 1 "Write code" "Implement board system in Rust"
show_board 1
exit
I can also extend this to persist data to a file or even make it a web API using Actix or Rocket if you want a more advanced version.

Do you want it to stay CLI only, or go web/API-based?




Attach

Search

Study

Voice
No file chosenNo file chosen
ChatGPT can make mistakes. Check important info.
