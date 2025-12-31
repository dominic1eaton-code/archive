// pms.rs

struct ProductionManagementSystem {
    production_line: Vec<String>,
    completed_tasks: Vec<String>,
}

impl ProductionManagementSystem {
    fn new() -> Self {
        ProductionManagementSystem {
            production_line: Vec::new(),
            completed_tasks: Vec::new(),
        }
    }

    fn add_task(&mut self, task: String) {
        self.production_line.push(task);
    }

    fn complete_task(&mut self) -> Option<String> {
        if let Some(task) = self.production_line.pop() {
            self.completed_tasks.push(task.clone());
            Some(task)
        } else {
            None
        }
    }

    fn list_tasks(&self) {
        println!("Production Line Tasks:");
        for task in &self.production_line {
            println!("- {}", task);
        }
    }

    fn list_completed_tasks(&self) {
        println!("Completed Tasks:");
        for task in &self.completed_tasks {
            println!("- {}", task);
        }
    }
}

fn main() {
    let mut pms = ProductionManagementSystem::new();
    
    pms.add_task("Assemble product A".to_string());
    pms.add_task("Quality check product B".to_string());
    
    pms.list_tasks();
    
    pms.complete_task();
    
    pms.list_tasks();
    pms.list_completed_tasks();
}