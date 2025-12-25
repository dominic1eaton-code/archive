const std = @import("std");

pub const Employee = struct {
    id: u32,
    name: []const u8,
    role: []const u8,
};

pub const Project = struct {
    id: u32,
    name: []const u8,
    status: []const u8,
};

pub const Task = struct {
    id: u32,
    description: []const u8,
    assigned_to: u32, // Employee ID
    status: []const u8,
};

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
            std.debug.print("ID: {}, Name: {}, Version: {}, Price: ${}, Status: {}\n", .{ product.id, product.name, product.version, product.price, statusToString(product.status) });
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
                std.debug.print("Cannot build product {}. Status: {}\n", .{ p.name, statusToString(p.status) });
                return;
            }
            p.status = ProductStatus.Built;
            std.debug.print("Product {} built.\n", .{p.name});
        } else {
            std.debug.print("Product ID {} not found.\n", .{id});
        }
    }

    pub fn testProduct(self: *SoftwareFactory, id: u32) void {
        if (self.findProduct(id)) |*p| {
            if (p.status != ProductStatus.Built) {
                std.debug.print("Cannot test product {}. Status: {}\n", .{ p.name, statusToString(p.status) });
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
                std.debug.print("Cannot release product {}. Status: {}\n", .{ p.name, statusToString(p.status) });
                return;
            }
            p.status = ProductStatus.Released;
            std.debug.print("Product {} released.\n", .{p.name});
        } else {
            std.debug.print("Product ID {} not found.\n", .{id});
        }
    }
};

fn addEmployee(factory: *Factory, id: u32, name: []const u8, role: []const u8) !void {
    const emp = Employee{
        .id = id,
        .name = name,
        .role = role,
    };
    // Simple append logic (manual, for dynamic arrays you'd realloc)
}

fn listEmployees(factory: *Factory) void {
    for (factory.employees) |emp| {
        std.debug.print("ID: {}, Name: {}, Role: {}\n", .{ emp.id, emp.name, emp.role });
    }
}
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
        std.debug.print("\nFound product {}: {} v{} at ${}\n", .{ p.id, p.name, p.version, p.price });
    } else {
        std.debug.print("\nProduct with ID {} not found\n", .{searchId});
    }
}

pub fn run_factory() !void {
    var stdout = std.io.getStdOut().writer();

    var employees: [10]Employee = undefined;
    var projects: [10]Project = undefined;
    var tasks: [10]Task = undefined;

    var factory = Factory{
        .employees = employees[0..0],
        .projects = projects[0..0],
        .tasks = tasks[0..0],
    };

    // Example: Add an employee
    const e = Employee{ .id = 1, .name = "Alice", .role = "Developer" };
    factory.employees = factory.employees ++ [_]Employee{e};

    // List employees
    listEmployees(&factory);
}
