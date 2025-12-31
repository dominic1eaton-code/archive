use std::collections::HashMap;
use std::fmt;

/// Unique identifier for entities
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct EntityId(u64);

impl EntityId {
    pub fn new(id: u64) -> Self {
        EntityId(id)
    }
}

/// Trait for entity types
pub trait Entity: Send + Sync {
    fn id(&self) -> EntityId;
    fn name(&self) -> &str;
    fn entity_type(&self) -> &str;
}

/// Generic business entity
#[derive(Debug, Clone)]
pub struct BusinessEntity {
    id: EntityId,
    name: String,
    entity_type: String,
    metadata: HashMap<String, String>,
}

impl BusinessEntity {
    pub fn new(id: u64, name: String, entity_type: String) -> Self {
        BusinessEntity {
            id: EntityId::new(id),
            name,
            entity_type,
            metadata: HashMap::new(),
        }
    }

    pub fn with_metadata(mut self, key: String, value: String) -> Self {
        self.metadata.insert(key, value);
        self
    }

    pub fn get_metadata(&self, key: &str) -> Option<&String> {
        self.metadata.get(key)
    }
}

impl Entity for BusinessEntity {
    fn id(&self) -> EntityId {
        self.id
    }

    fn name(&self) -> &str {
        &self.name
    }

    fn entity_type(&self) -> &str {
        &self.entity_type
    }
}

/// Entity manager
pub struct EntityManager {
    entities: HashMap<EntityId, Box<dyn Entity>>,
}

impl EntityManager {
    pub fn new() -> Self {
        EntityManager {
            entities: HashMap::new(),
        }
    }

    pub fn register(&mut self, entity: Box<dyn Entity>) {
        self.entities.insert(entity.id(), entity);
    }

    pub fn get(&self, id: EntityId) -> Option<&dyn Entity> {
        self.entities.get(&id).map(|e| e.as_ref())
    }

    pub fn remove(&mut self, id: EntityId) -> bool {
        self.entities.remove(&id).is_some()
    }

    pub fn list(&self) -> Vec<(EntityId, &str, &str)> {
        self.entities
            .values()
            .map(|e| (e.id(), e.name(), e.entity_type()))
            .collect()
    }
}

impl Default for EntityManager {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_entity_manager() {
        let mut manager = EntityManager::new();
        let entity = Box::new(BusinessEntity::new(
            1,
            "Company A".to_string(),
            "Corporation".to_string(),
        ));
        manager.register(entity);
        assert!(manager.get(EntityId::new(1)).is_some());
    }
}