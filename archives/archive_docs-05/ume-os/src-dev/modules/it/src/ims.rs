// ims.rs

pub struct ITManagementSystem {
    assets: Vec<Asset>,
}

#[derive(Debug)]
pub struct Asset {
    id: u32,
    name: String,
    asset_type: String,
}

impl ITManagementSystem {
    pub fn new() -> Self {
        ITManagementSystem {
            assets: Vec::new(),
        }
    }

    pub fn add_asset(&mut self, id: u32, name: String, asset_type: String) {
        let asset = Asset { id, name, asset_type };
        self.assets.push(asset);
    }

    pub fn list_assets(&self) {
        for asset in &self.assets {
            println!("{:?}", asset);
        }
    }
}

fn main() {
    let mut it_system = ITManagementSystem::new();
    it_system.add_asset(1, String::from("Laptop"), String::from("Hardware"));
    it_system.add_asset(2, String::from("Office 365"), String::from("Software"));
    
    it_system.list_assets();
}

// Additional functionality to remove an asset by ID
pub fn remove_asset(&mut self, id: u32) {
    self.assets.retain(|asset| asset.id != id);
}

// Example usage of remove_asset
it_system.remove_asset(1);
it_system.list_assets();

// Additional functionality to manage servers
#[derive(Debug)]
pub struct Server {
    id: u32,
    name: String,
    ip_address: String,
}

impl ITManagementSystem {
    pub fn add_server(&mut self, id: u32, name: String, ip_address: String) {
        let server = Server { id, name, ip_address };
        // Assuming you want to store servers in a separate vector
        // self.servers.push(server); // Uncomment if you have a servers field
    }

    pub fn list_servers(&self) {
        // Assuming you have a servers field
        // for server in &self.servers {
        //     println!("{:?}", server);
        // }
    }

    pub fn remove_server(&mut self, id: u32) {
        // Assuming you have a servers field
        // self.servers.retain(|server| server.id != id);
    }
}