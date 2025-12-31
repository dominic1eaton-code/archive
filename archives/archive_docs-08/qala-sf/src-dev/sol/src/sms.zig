// solution management system
const std = @import("std");

const Product = struct {
    id: u32,
    name: []const u8,
    version: []const u8,
    price: f64,
};

const SoftwareFactory = struct {
    allocator: *std.mem.Allocator,
    products: std.ArrayList(Product),

    pub fn init(allocator: *std.mem.Allocator) SoftwareFactory {
        return SoftwareFactory{
            .allocator = allocator,
            .products = std.ArrayList(Product).init(allocator),
        };
    }

    pub fn createProduct(self: *SoftwareFactory, id: u32, name: []const u8, version: []const u8, price: f64) !void {
        try self.products.append(Product{
            .id = id,
            .name = name,
            .version = version,
            .price = price,
        });
        std.debug.print("Product created: {} v{} (${})\n", .{name, version, price});
    }

    pub fn listProducts(self: *SoftwareFactory) void {
        if (self.products.items.len == 0) {
            std.debug.print("No products available.\n", .{});
            return;
        }

        for (self.products.items) |product| {
            std.debug.print("ID: {}, Name: {}, Version: {}, Price: ${}\n", 
                .{product.id, product.name, product.version, product.price});
        }
    }

    pub fn findProduct(self: *SoftwareFactory, id: u32) ?*Product {
        for (self.products.items) |*p| {
            if (p.id == id) return p;
        }
        return null;
    }
};

pub fn main() !void {
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    const allocator = &gpa.allocator;

    var factory = SoftwareFactory.init(allocator);

    // Create a few products
    try factory.createProduct(1, "Zig Compiler", "0.11.0", 0.0);
    try factory.createProduct(2, "Zig Book", "1.0", 29.99);
    try factory.createProduct(3, "Zig IDE", "0.1", 49.99);

    std.debug.print("\nListing all products:\n", .{});
    factory.listProducts();

    const searchId = 2;
    if (factory.findProduct(searchId)) |p| {
        std.debug.print("\nFound product {}: {} v{} at ${}\n", .{p.id, p.name, p.version, p.price});
    } else {
        std.debug.print("\nProduct with ID {} not found\n", .{searchId});
    }
}
