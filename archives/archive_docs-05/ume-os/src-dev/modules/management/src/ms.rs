use std::collections::HashMap;

// ms.rs


struct Dashboard {
    metrics: HashMap<String, f64>,
}

impl Dashboard {
    fn new() -> Self {
        Dashboard {
            metrics: HashMap::new(),
        }
    }

    fn add_metric(&mut self, name: String, value: f64) {
        self.metrics.insert(name, value);
    }

    fn display(&self) {
        println!("Enterprise Management Dashboard:");
        for (name, value) in &self.metrics {
            println!("{}: {}", name, value);
        }
    }
}


fn calculate_kpi(&self, kpi_name: &str) -> Option<f64> {
    self.metrics.get(kpi_name).cloned()
}

fn display_kpi(&self, kpi_name: &str) {
    match self.calculate_kpi(kpi_name) {
        Some(value) => println!("KPI - {}: {}", kpi_name, value),
        None => println!("KPI - {} not found.", kpi_name),
    }
}

// Example usage of the KPI management system
dashboard.display_kpi("Active Users");
dashboard.display_kpi("Total Revenue");
dashboard.display_kpi("Nonexistent KPI");

fn main() {
    let mut dashboard = Dashboard::new();
    dashboard.add_metric("Active Users".to_string(), 1500.0);
    dashboard.add_metric("Total Revenue".to_string(), 25000.0);
    dashboard.add_metric("System Uptime".to_string(), 99.9);
    
    dashboard.display();
}