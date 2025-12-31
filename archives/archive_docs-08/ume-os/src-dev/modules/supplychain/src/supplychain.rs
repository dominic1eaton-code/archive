use std::collections::HashMap;

#[derive(Clone, Debug)]
pub struct Product {
    id: String,
    name: String,
    quantity: u32,
    price: f64,
}

#[derive(Clone, Debug)]
pub struct Supplier {
    id: String,
    name: String,
    location: String,
}

#[derive(Clone, Debug)]
pub struct Order {
    id: String,
    product_id: String,
    supplier_id: String,
    quantity: u32,
    status: OrderStatus,
}

#[derive(Clone, Debug, PartialEq)]
pub enum OrderStatus {
    Pending,
    Shipped,
    Delivered,
    Cancelled,
}

pub struct SupplyChain {
    products: HashMap<String, Product>,
    suppliers: HashMap<String, Supplier>,
    orders: HashMap<String, Order>,
}

impl SupplyChain {
    pub fn new() -> Self {
        SupplyChain {
            products: HashMap::new(),
            suppliers: HashMap::new(),
            orders: HashMap::new(),
        }
    }

    pub fn add_product(&mut self, product: Product) {
        self.products.insert(product.id.clone(), product);
    }

    pub fn add_supplier(&mut self, supplier: Supplier) {
        self.suppliers.insert(supplier.id.clone(), supplier);
    }

    pub fn create_order(&mut self, order: Order) -> Result<(), String> {
        if !self.products.contains_key(&order.product_id) {
            return Err("Product not found".to_string());
        }
        if !self.suppliers.contains_key(&order.supplier_id) {
            return Err("Supplier not found".to_string());
        }
        self.orders.insert(order.id.clone(), order);
        Ok(())
    }

    pub fn update_order_status(&mut self, order_id: &str, status: OrderStatus) -> Result<(), String> {
        self.orders
            .get_mut(order_id)
            .ok_or("Order not found".to_string())
            .map(|order| order.status = status)
    }

    pub fn get_order(&self, order_id: &str) -> Option<&Order> {
        self.orders.get(order_id)
    }
}