use std::collections::HashMap;

// ims.rs


#[derive(Debug)]
struct Item {
    id: u32,
    name: String,
    quantity: u32,
}

struct Inventory {
    items: HashMap<u32, Item>,
}

impl Inventory {
    fn new() -> Self {
        Inventory {
            items: HashMap::new(),
        }
    }

    fn add_item(&mut self, id: u32, name: String, quantity: u32) {
        let item = Item { id, name, quantity };
        self.items.insert(id, item);
    }

    fn remove_item(&mut self, id: u32) {
        self.items.remove(&id);
    }

    fn update_quantity(&mut self, id: u32, quantity: u32) {
        if let Some(item) = self.items.get_mut(&id) {
            item.quantity = quantity;
        }
    }

    fn get_item(&self, id: u32) -> Option<&Item> {
        self.items.get(&id)
    }

    fn list_items(&self) {
        for item in self.items.values() {
            println!("{:?}", item);
        }
    }
}

fn main() {
    let mut inventory = Inventory::new();
    
    inventory.add_item(1, String::from("Widget"), 10);
    inventory.add_item(2, String::from("Gadget"), 5);
    
    inventory.list_items();
    
    inventory.update_quantity(1, 15);
    inventory.remove_item(2);
    
    inventory.list_items();
}