// src/rms.rs

#[derive(Debug)]
struct RiskRegister {
    risks: Vec<Risk>,
}

impl RiskRegister {
    fn new() -> Self {
        RiskRegister { risks: Vec::new() }
    }

    fn add_risk(&mut self, risk: Risk) {
        self.risks.push(risk);
    }

    fn list_risks(&self) {
        for risk in &self.risks {
            println!("{:?}", risk);
        }
    }
}

#[derive(Debug)]
struct Risk {
    id: u32,
    description: String,
    likelihood: f32, // Probability of occurrence
    impact: f32,     // Impact severity
}

impl Risk {
    fn new(id: u32, description: &str, likelihood: f32, impact: f32) -> Self {
        Risk {
            id,
            description: description.to_string(),
            likelihood,
            impact,
        }
    }

    fn risk_score(&self) -> f32 {
        self.likelihood * self.impact
    }
}

struct RiskManagementSystem {
    risks: Vec<Risk>,
}

impl RiskManagementSystem {
    fn new() -> Self {
        RiskManagementSystem { risks: Vec::new() }
    }

    fn add_risk(&mut self, risk: Risk) {
        self.risks.push(risk);
    }

    fn total_risk_score(&self) -> f32 {
        self.risks.iter().map(|risk| risk.risk_score()).sum()
    }
}

fn main() {
    let mut rms = RiskManagementSystem::new();

    let risk1 = Risk::new(1, "Data breach", 0.7, 9.0);
    let risk2 = Risk::new(2, "Server downtime", 0.5, 7.0);

    rms.add_risk(risk1);
    rms.add_risk(risk2);

    println!("Total Risk Score: {}", rms.total_risk_score());
}