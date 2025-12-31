// ems.rs

struct EngineeringSolution {
    id: u32,
    name: String,
    description: String,
    status: String,
}

impl EngineeringSolution {
    fn new(id: u32, name: &str, description: &str, status: &str) -> Self {
        EngineeringSolution {
            id,
            name: name.to_string(),
            description: description.to_string(),
            status: status.to_string(),
        }
    }

    fn update_status(&mut self, new_status: &str) {
        self.status = new_status.to_string();
    }
}

struct EngineeringSolutionManager {
    solutions: Vec<EngineeringSolution>,
}

impl EngineeringSolutionManager {
    fn new() -> Self {
        EngineeringSolutionManager {
            solutions: Vec::new(),
        }
    }

    fn add_solution(&mut self, solution: EngineeringSolution) {
        self.solutions.push(solution);
    }

    fn get_solution(&self, id: u32) -> Option<&EngineeringSolution> {
        self.solutions.iter().find(|&s| s.id == id)
    }
}

fn main() {
    let mut manager = EngineeringSolutionManager::new();
    
    let solution1 = EngineeringSolution::new(1, "Solution A", "Description of Solution A", "Active");
    manager.add_solution(solution1);

    if let Some(solution) = manager.get_solution(1) {
        println!("Found solution: {} - {}", solution.name, solution.status);
    }
}