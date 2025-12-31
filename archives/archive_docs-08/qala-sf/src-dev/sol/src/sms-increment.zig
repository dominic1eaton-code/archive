const std = @import("std");

const ProductStatus = enum {
    Created,
    Built,
    Tested,
    Released,
};

fn statusToString(status: ProductStatus) []const u8 {
    return switch (status) {
        .Created => "Created",
        .Built => "Built",
        .Tested => "Tested",
        .Released => "Released",
    };
}

fn stringToStatus(s: []const u8) ProductStatus {
    if (std.mem.eql(u8, s, "Created")) return ProductStatus.Created;
    if (std.mem.eql(u8, s, "Built")) return ProductStatus.Built;
    if (std.mem.eql(u8, s, "Tested")) return ProductStatus.Tested;
    if (std.mem.eql(u8, s, "Released")) return ProductStatus.Released;
    return ProductStatus.Created; // default fallback
}

const BuildHistory = struct {
    timestamp: u64,
    version: []const u8,
};

const Product = struct {
    id: u32,
    name: []const u8,
    version: []const u8,
    price: f64,
    status: ProductStatus,
    history: std.ArrayList(BuildHistory),

    pub fn init(allocator: *std.mem.Allocator, id: u32, name: []const u8, version: []const u8, price: f64) !Product {
        return Product{
            .id = id,
            .name = name,
            .version = version,
            .price = price,
            .status = ProductStatus.Created,
            .history = std.ArrayList(BuildHistory).init(allocator),
        };
    }

    pub fn incrementVersion(self: *Product, allocator: *std.mem.Allocator) !void {
        // Expect version in "major.minor" format
        var major: u32 = 0;
        var minor: u32 = 0;
        var parts = std.mem.split(self.version, ".");
        var it = parts.iterator();
        if (it.next()) |part| {
            major = try std.fmt.parseInt(u32, part, 10);
        }
        if (it.next()) |part| {
            minor = try std.fmt.parseInt(u32, part, 10);
        }
        minor += 1; // increment minor version
        const new_version = try std.fmt.allocPrint(allocator, "{d}.{d}", .{major, minor});
        self.version = new_version;

        // Add to build history
        const now = try std.time.milliTimestamp();
        try self.history.append(BuildHistory{ .timestamp=now, .version=self.version });
    }
};

const SoftwareFactory = struct {
    allocator: *std.mem.Allocator,
    products: std.ArrayList(Product>,
    data_file: []const u8,

    pub fn init(allocator: *std.mem.Allocator, data_file: []const u8) SoftwareFactory {
        return SoftwareFactory{
            .allocator = allocator,
            .products = std.ArrayList(Product).init(allocator),
            .data_file = data_file,
        };
    }

    pub fn createProduct(self: *SoftwareFactory, id: u32, name: []const u8, version: []const u8, price: f64) !void {
        const product = try Product.init(self.allocator, id, name, version, price);
        try self.products.append(product);
        std.debug.print("Product created: {} v{} (${})\n", .{name, version, price});
    }

    pub fn findProduct(self: *SoftwareFactory, id: u32) ?*Product {
        for (self.products.items) |*p| {
            if (p.id == id) return p;
        }
        return null;
    }

    pub fn listProducts(self: *SoftwareFactory) void {
        if (self.products.items.len == 0) {
            std.debug.print("No products available.\n", .{});
            return;
        }
        for (self.products.items) |product| {
            std.debug.print("ID: {}, Name: {}, Version: {}, Price: ${}, Status: {}\n",
                .{product.id, product.name, product.version, product.price, statusToString(product.status)});
            if (product.history.items.len > 0) {
                std.debug.print("  Build History:\n", .{});
                for (product.history.items) |h| {
                    std.debug.print("    - Version: {}, Timestamp: {d}\n", .{h.version, h.timestamp});
                }
            }
        }
    }

    pub fn buildProduct(self: *SoftwareFactory, id: u32) !void {
        if (self.findProduct(id)) |*p| {
            if (p.status != ProductStatus.Created) {
                std.debug.print("Cannot build product {}. Status: {}\n", .{p.name, statusToString(p.status)});
                return;
            }
            try p.incrementVersion(self.allocator);
            p.status = ProductStatus.Built;
            std.debug.print("Product {} built. New version: {}\n", .{p.name, p.version});
        } else {
            std.debug.print("Product ID {} not found.\n", .{id});
        }
    }

    pub fn testProduct(self: *SoftwareFactory, id: u32) void {
        if (self.findProduct(id)) |*p| {
            if (p.status != ProductStatus.Built) {
                std.debug.print("Cannot test product {}. Status: {}\n", .{p.name, statusToString(p.status)});
                return;
            }
            p.status = ProductStatus.Tested;
            std.debug.print("Product {} tested.\n", .{p.name});
        } else {
            std.debug.print("Product ID {} not found.\n", .{id});
        }
    }

    pub fn releaseProduct(self: *SoftwareFactory, id: u32) void {
        if (self.findProduct(id)) |*p| {
            if (p.status != ProductStatus.Tested) {
                std.debug.print("Cannot release product {}. Status: {}\n", .{p.name, statusToString(p.status)});
                return;
            }
            p.status = ProductStatus.Released;
            std.debug.print("Product {} released.\n", .{p.name});
        } else {
            std.debug.print("Product ID {} not found.\n", .{id});
        }
    }
};

pub fn main() !void {
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    const allocator = &gpa.allocator;

    var factory = SoftwareFactory.init(allocator, "products.json");

    // Minimal console example
    try factory.createProduct(1, "Zig Compiler", "0.11", 0.0);
    try factory.buildProduct(1);
    factory.testProduct(1);
    factory.releaseProduct(1);

    factory.listProducts();

    try factory.createProduct(2, "Zig Book", "1.0", 29.99);

    // Build, test, and release first product
    try factory.buildProduct(1);
    factory.testProduct(1);
    factory.releaseProduct(1);

    // List all products
    factory.listProducts();
}