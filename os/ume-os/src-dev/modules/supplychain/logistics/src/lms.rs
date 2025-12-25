// lms.rs

struct Shipment {
    id: u32,
    origin: String,
    destination: String,
    status: ShipmentStatus,
}

enum ShipmentStatus {
    Pending,
    InTransit,
    Delivered,
    Canceled,
}

impl Shipment {
    fn new(id: u32, origin: String, destination: String) -> Self {
        Shipment {
            id,
            origin,
            destination,
            status: ShipmentStatus::Pending,
        }
    }

    fn update_status(&mut self, status: ShipmentStatus) {
        self.status = status;
    }
}

struct LogisticsManager {
    shipments: Vec<Shipment>,
}

impl LogisticsManager {
    fn new() -> Self {
        LogisticsManager {
            shipments: Vec::new(),
        }
    }

    fn add_shipment(&mut self, shipment: Shipment) {
        self.shipments.push(shipment);
    }

    fn get_shipment(&self, id: u32) -> Option<&Shipment> {
        self.shipments.iter().find(|&s| s.id == id)
    }
}

fn main() {
    let mut manager = LogisticsManager::new();
    let shipment = Shipment::new(1, String::from("New York"), String::from("Los Angeles"));
    
    manager.add_shipment(shipment);
    
    if let Some(shipment) = manager.get_shipment(1) {
        println!("Shipment ID: {}, Status: {:?}", shipment.id, shipment.status);
    }
}