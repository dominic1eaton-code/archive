// dms.rs

pub struct DesignSystem {
    pub colors: Vec<String>,
    pub typography: Vec<String>,
    pub spacing: Vec<u32>,
}

impl DesignSystem {
    pub fn new() -> Self {
        DesignSystem {
            colors: vec![],
            typography: vec![],
            spacing: vec![],
        }
    }

    pub fn add_color(&mut self, color: String) {
        self.colors.push(color);
    }

    pub fn add_typography(&mut self, font: String) {
        self.typography.push(font);
    }

    pub fn add_spacing(&mut self, space: u32) {
        self.spacing.push(space);
    }

    pub fn remove_color(&mut self, color: &str) {
        self.colors.retain(|c| c != color);
    }

    pub fn remove_typography(&mut self, font: &str) {
        self.typography.retain(|f| f != font);
    }

    pub fn remove_spacing(&mut self, space: u32) {
        self.spacing.retain(|&s| s != space);
    }
    pub fn display(&self) {
        println!("Colors: {:?}", self.colors);
        println!("Typography: {:?}", self.typography);
        println!("Spacing: {:?}", self.spacing);
    }
}