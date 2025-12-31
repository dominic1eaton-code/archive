const std = @import("std");

const ProductStatus = enum {
    Created,
    Built,
    Tested,
    Released,
};

const Product = struct {
    id: u32,
    name: []const u8,
    version: []const u8,
    price: f64,
    status: ProductStatus,
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
            .status = ProductStatus.Created,
        });
        std.debug.print("Product created: {} v{} (${})\n", .{ name, version, price });
    }

    pub fn listProducts(self: *SoftwareFactory) void {
        if (self.products.items.len == 0) {
            std.debug.print("No products available.\n", .{});
            return;
        }

        for (self.products.items) |product| {
            std.debug.print("ID: {}, Name: {}, Version: {}, Price: ${}, Status: {}\n", .{ product.id, product.name, product.version, product.price, product.status });
        }
    }

    pub fn findProduct(self: *SoftwareFactory, id: u32) ?*Product {
        for (self.products.items) |*p| {
            if (p.id == id) return p;
        }
        return null;
    }

    pub fn buildProduct(self: *SoftwareFactory, id: u32) void {
        if (self.findProduct(id)) |*p| {
            if (p.status != ProductStatus.Created) {
                std.debug.print("Product {} cannot be built. Current status: {}\n", .{ p.name, p.status });
                return;
            }
            p.status = ProductStatus.Built;
            std.debug.print("Product {} v{} has been built.\n", .{ p.name, p.version });
        } else {
            std.debug.print("Product with ID {} not found.\n", .{id});
        }
    }

    pub fn testProduct(self: *SoftwareFactory, id: u32) void {
        if (self.findProduct(id)) |*p| {
            if (p.status != ProductStatus.Built) {
                std.debug.print("Product {} cannot be tested. Current status: {}\n", .{ p.name, p.status });
                return;
            }
            p.status = ProductStatus.Tested;
            std.debug.print("Product {} v{} has passed testing.\n", .{ p.name, p.version });
        } else {
            std.debug.print("Product with ID {} not found.\n", .{id});
        }
    }

    pub fn releaseProduct(self: *SoftwareFactory, id: u32) void {
        if (self.findProduct(id)) |*p| {
            if (p.status != ProductStatus.Tested) {
                std.debug.print("Product {} cannot be released. Current status: {}\n", .{ p.name, p.status });
                return;
            }
            p.status = ProductStatus.Released;
            std.debug.print("Product {} v{} has been released!\n", .{ p.name, p.version });
        } else {
            std.debug.print("Product with ID {} not found.\n", .{id});
        }
    }
};

pub fn main() !void {
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    const allocator = &gpa.allocator;

    var factory = SoftwareFactory.init(allocator);

    // Create sample products
    try factory.createProduct(1, "Zig Compiler", "0.11.0", 0.0);
    try factory.createProduct(2, "Zig Book", "1.0", 29.99);
    try factory.createProduct(3, "Zig IDE", "0.1", 49.99);

    std.debug.print("\n--- Initial Product List ---\n", .{});
    factory.listProducts();

    // Simulate the software factory pipeline
    std.debug.print("\n--- Building Products ---\n", .{});
    factory.buildProduct(1);
    factory.buildProduct(2);

    std.debug.print("\n--- Testing Products ---\n", .{});
    factory.testProduct(1);
    factory.testProduct(3); // Should fail (not built)

    std.debug.print("\n--- Releasing Products ---\n", .{});
    factory.releaseProduct(1);
    factory.releaseProduct(2); // Should fail (not tested)

    std.debug.print("\n--- Final Product List ---\n", .{});
    factory.listProducts();
    
    std.debug.print("\n--- Initial Product List ---\n", .{});
    factory.listProducts();

    // Simulate the software factory pipeline
    std.debug.print("\n--- Building Products ---\n", .{});
    factory.buildProduct(1);
    factory.buildProduct(2);

    std.debug.print("\n--- Testing Products ---\n", .{});
    factory.testProduct(1);
    factory.testProduct(3); // Should fail (not built)

    std.debug.print("\n--- Releasing Products ---\n", .{});
    factory.releaseProduct(1);
    factory.releaseProduct(2); // Should fail (not tested)

    std.debug.print("\n--- Final Product List ---\n", .{});
    factory.listProducts();
}
