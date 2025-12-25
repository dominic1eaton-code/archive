use std::collections::HashMap;
use chrono::{DateTime, Utc};

#[derive(Debug, Clone)]
pub struct Benefit {
    pub id: String,
    pub name: String,
    pub description: String,
    pub benefit_type: BenefitType,
    pub cost_per_month: f64,
    pub is_active: bool,
}

#[derive(Debug, Clone)]
pub enum BenefitType {
    HealthInsurance,
    DentalInsurance,
    VisionInsurance,
    RetirementPlan,
    PaidTimeOff,
    LifeInsurance,
    FlexibleSpending,
}

#[derive(Debug, Clone)]
pub struct EmployeeBenefit {
    pub employee_id: String,
    pub benefit_id: String,
    pub enrolled_date: DateTime<Utc>,
    pub is_enrolled: bool,
    pub coverage_level: String,
}

pub struct BenefitsManager {
    benefits: HashMap<String, Benefit>,
    employee_benefits: HashMap<String, Vec<EmployeeBenefit>>,
}

impl BenefitsManager {
    pub fn new() -> Self {
        BenefitsManager {
            benefits: HashMap::new(),
            employee_benefits: HashMap::new(),
        }
    }

    pub fn add_benefit(&mut self, benefit: Benefit) {
        self.benefits.insert(benefit.id.clone(), benefit);
    }

    pub fn enroll_employee(&mut self, employee_id: String, benefit_id: String, coverage_level: String) -> Result<(), String> {
        if !self.benefits.contains_key(&benefit_id) {
            return Err("Benefit not found".to_string());
        }

        let employee_benefit = EmployeeBenefit {
            employee_id: employee_id.clone(),
            benefit_id,
            enrolled_date: Utc::now(),
            is_enrolled: true,
            coverage_level,
        };

        self.employee_benefits
            .entry(employee_id)
            .or_insert_with(Vec::new)
            .push(employee_benefit);

        Ok(())
    }

    pub fn get_employee_benefits(&self, employee_id: &str) -> Option<Vec<EmployeeBenefit>> {
        self.employee_benefits.get(employee_id).cloned()
    }

    pub fn calculate_total_cost(&self, employee_id: &str) -> f64 {
        self.employee_benefits
            .get(employee_id)
            .map(|benefits| {
                benefits
                    .iter()
                    .filter(|eb| eb.is_enrolled)
                    .filter_map(|eb| self.benefits.get(&eb.benefit_id))
                    .map(|b| b.cost_per_month)
                    .sum()
            })
            .unwrap_or(0.0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_add_benefit() {
        let mut manager = BenefitsManager::new();
        let benefit = Benefit {
            id: "health-001".to_string(),
            name: "Health Insurance".to_string(),
            description: "Comprehensive health coverage".to_string(),
            benefit_type: BenefitType::HealthInsurance,
            cost_per_month: 450.0,
            is_active: true,
        };
        manager.add_benefit(benefit);
        assert_eq!(manager.benefits.len(), 1);
    }
}