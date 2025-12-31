use std::collections::HashMap;

#[derive(Clone, Debug)]
pub struct Product {
    pub id: u32,
    pub name: String,
    pub price: f64,
    pub quantity: u32,
}

#[derive(Clone, Debug)]
pub struct SaleItem {
    pub product_id: u32,
    pub quantity: u32,
    pub unit_price: f64,
}

#[derive(Clone, Debug)]
pub struct Sale {
    pub id: u32,
    pub items: Vec<SaleItem>,
    pub total: f64,
}

pub struct SalesManager {
    products: HashMap<u32, Product>,
    sales: HashMap<u32, Sale>,
    next_sale_id: u32,
}

impl SalesManager {
    pub fn new() -> Self {
        SalesManager {
            products: HashMap::new(),
            sales: HashMap::new(),
            next_sale_id: 1,
        }
    }

    pub fn add_product(&mut self, product: Product) {
        self.products.insert(product.id, product);
    }

    pub fn create_sale(&mut self, items: Vec<SaleItem>) -> Result<Sale, String> {
        let mut total = 0.0;
        
        for item in &items {
            let product = self.products.get(&item.product_id)
                .ok_or("Product not found")?;
            
            if product.quantity < item.quantity {
                return Err("Insufficient inventory".to_string());
            }
            
            total += item.unit_price * item.quantity as f64;
        }

        let sale = Sale {
            id: self.next_sale_id,
            items,
            total,
        };
        
        self.sales.insert(self.next_sale_id, sale.clone());
        self.next_sale_id += 1;
        
        Ok(sale)
    }

    pub fn get_sales(&self) -> Vec<Sale> {
        self.sales.values().cloned().collect()
    }

    pub fn get_total_revenue(&self) -> f64 {
        self.sales.values().map(|s| s.total).sum()
    }
}