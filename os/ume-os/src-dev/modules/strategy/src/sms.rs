use std::collections::HashMap;
use std::fmt;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum StrategyType {
    Offensive,
    Defensive,
    Balanced,
    Custom(String),
}

#[derive(Debug, Clone)]
pub struct Strategy {
    pub id: String,
    pub name: String,
    pub strategy_type: StrategyType,
    pub priority: u8,
    pub active: bool,
}

#[derive(Debug)]
pub struct StrategicManagementSystem {
    strategies: HashMap<String, Strategy>,
    active_strategy: Option<String>,
}

impl StrategicManagementSystem {
    pub fn new() -> Self {
        Self {
            strategies: HashMap::new(),
            active_strategy: None,
        }
    }

    pub fn add_strategy(&mut self, strategy: Strategy) -> Result<(), String> {
        if self.strategies.contains_key(&strategy.id) {
            return Err(format!("Strategy {} already exists", strategy.id));
        }
        self.strategies.insert(strategy.id.clone(), strategy);
        Ok(())
    }

    pub fn activate_strategy(&mut self, id: &str) -> Result<(), String> {
        if !self.strategies.contains_key(id) {
            return Err(format!("Strategy {} not found", id));
        }
        self.active_strategy = Some(id.to_string());
        Ok(())
    }

    pub fn get_active_strategy(&self) -> Option<&Strategy> {
        self.active_strategy
            .as_ref()
            .and_then(|id| self.strategies.get(id))
    }

    pub fn list_strategies(&self) -> Vec<&Strategy> {
        self.strategies.values().collect()
    }

    pub fn remove_strategy(&mut self, id: &str) -> Result<Strategy, String> {
        self.strategies
            .remove(id)
            .ok_or_else(|| format!("Strategy {} not found", id))
    }
}

impl Default for StrategicManagementSystem {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_add_strategy() {
        let mut sms = StrategicManagementSystem::new();
        let strategy = Strategy {
            id: "strat1".to_string(),
            name: "Aggressive Growth".to_string(),
            strategy_type: StrategyType::Offensive,
            priority: 1,
            active: false,
        };
        assert!(sms.add_strategy(strategy).is_ok());
    }

    #[test]
    fn test_activate_strategy() {
        let mut sms = StrategicManagementSystem::new();
        let strategy = Strategy {
            id: "strat1".to_string(),
            name: "Test Strategy".to_string(),
            strategy_type: StrategyType::Balanced,
            priority: 5,
            active: false,
        };
        sms.add_strategy(strategy).unwrap();
        assert!(sms.activate_strategy("strat1").is_ok());
        assert!(sms.get_active_strategy().is_some());
    }
}