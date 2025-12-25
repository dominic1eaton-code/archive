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
    data_file: []const u8,

    pub fn init(allocator: *std.mem.Allocator, data_file: []const u8) SoftwareFactory {
        return SoftwareFactory{
            .allocator = allocator,
            .products = std.ArrayList(Product).init(allocator),
            .data_file = data_file,
        };
    }

    pub fn save(self: *SoftwareFactory) !void {
        var file = try std.fs.cwd().createFile(self.data_file, .{ .truncate = true });
        defer file.close();

        try file.writeAll("[\n");
        for (self.products.items) |product, i| {
            const json_line = std.fmt.allocPrint(self.allocator,
                "  {{\"id\":{d},\"name\":\"{s}\",\"version\":\"{s}\",\"price\":{f},\"status\":\"{s}\"}}{s}\n",
                .{product.id, product.name, product.version, product.price, statusToString(product.status),
                  if (i == self.products.items.len - 1) "" else ","});
            defer self.allocator.free(json_line);

            try file.writeAll(json_line);
        }
        try file.writeAll("]\n");
        std.debug.print("Products saved to file.\n", .{});
    }

    pub fn load(self: *SoftwareFactory) !void {
        const file = try std.fs.cwd().openFile(self.data_file, .{});
        defer file.close();

        var data = try file.readToEndAlloc(self.allocator, std.math.maxInt(usize));
        defer self.allocator.free(data);

        var reader = std.io.fixedBufferStream(data).reader();
        while (true) {
            const line = try reader.readUntilDelimiterOrEof('\n', self.allocator);
            if (line.len == 0) break;

            // Minimal JSON parsing
            if (std.mem.contains(u8, line, '{')) {
                var id: u32 = 0;
                var name: []const u8 = "";
                var version: []const u8 = "";
                var price: f64 = 0;
                var status: ProductStatus = ProductStatus.Created;

                _ = std.fmt.scan(line, "  {\"id\":{d},\"name\":\"{s}\",\"version\":\"{s}\",\"price\":{f},\"status\":\"{s}\"}",
                    .{ &id, &name, &version, &price, &status });
                try self.products.append(Product{ .id = id, .name = name, .version = version, .price = price, .status = status });
            }
        }
        std.debug.print("Products loaded from file.\n", .{});
    }

    pub fn listProducts(self: *SoftwareFactory) void {
        if (self.products.items.len == 0) {
            std.debug.print("No products available.\n", .{});
            return;
        }
        for (self.products.items) |product| {
            std.debug.print("ID: {}, Name: {}, Version: {}, Price: ${}, Status: {}\n",
                .{product.id, product.name, product.version, product.price, statusToString(product.status)});
        }
    }

    pub fn findProduct(self: *SoftwareFactory, id: u32) ?*Product {
        for (self.products.items) |*p| {
            if (p.id == id) return p;
        }
        return null;
    }

    pub fn createProduct(self: *SoftwareFactory, id: u32, name: []const u8, version: []const u8, price: f64) !void {
        try self.products.append(Product{ .id=id, .name=name, .version=version, .price=price, .status=ProductStatus.Created });
        std.debug.print("Product created: {} v{} (${})\n", .{name, version, price});
    }

    pub fn buildProduct(self: *SoftwareFactory, id: u32) void {
        if (self.findProduct(id)) |*p| {
            if (p.status != ProductStatus.Created) {
                std.debug.print("Cannot build product {}. Status: {}\n", .{p.name, statusToString(p.status)});
                return;
            }
            p.status = ProductStatus.Built;
            std.debug.print("Product {} built.\n", .{p.name});
        } else { std.debug.print("Product ID {} not found.\n", .{id}); }
    }

    pub fn testProduct(self: *SoftwareFactory, id: u32) void {
        if (self.findProduct(id)) |*p| {
            if (p.status != ProductStatus.Built) {
                std.debug.print("Cannot test product {}. Status: {}\n", .{p.name, statusToString(p.status)});
                return;
            }
            p.status = ProductStatus.Tested;
            std.debug.print("Product {} tested.\n", .{p.name});
        } else { std.debug.print("Product ID {} not found.\n", .{id}); }
    }

    pub fn releaseProduct(self: *SoftwareFactory, id: u32) void {
        if (self.findProduct(id)) |*p| {
            if (p.status != ProductStatus.Tested) {
                std.debug.print("Cannot release product {}. Status: {}\n", .{p.name, statusToString(p.status)});
                return;
            }
            p.status = ProductStatus.Released;
            std.debug.print("Product {} released.\n", .{p.name});
        } else { std.debug.print("Product ID {} not found.\n", .{id}); }
    }
};

pub fn main() !void {
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    const allocator = &gpa.allocator;

    var factory = SoftwareFactory.init(allocator, "products.json");
    _ = factory.load(); // ignore errors if file doesn't exist

    var stdin = std.io.getStdIn().reader();
    var stdout = std.io.getStdOut().writer();

    while (true) {
        try stdout.print("\n--- Software Factory Menu ---\n", .{});
        try stdout.print("1. Create Product\n2. List Products\n3. Build Product\n4. Test Product\n5. Release Product\n6. Save & Exit\nChoose option: ", .{});

        var line = try stdin.readLineAlloc(allocator, 1024);
        defer allocator.free(line);

        switch (line[0]) {
            '1' => {
                try stdout.print("Enter product ID: ", .{});
                const id = try stdin.readInt(u32, 10);
                try stdout.print("Enter product name: ", .{});
                const name = try stdin.readLineAlloc(allocator, 1024);
                defer allocator.free(name);
                try stdout.print("Enter version: ", .{});
                const version = try stdin.readLineAlloc(allocator, 1024);
                defer allocator.free(version);
                try stdout.print("Enter price: ", .{});
                const price = try stdin.readFloat(f64);
                try factory.createProduct(id, name, version, price);
            },
            '2' => factory.listProducts(),
            '3' => {
                try stdout.print("Enter product ID to build: ", .{});
                const id = try stdin.readInt(u32, 10);
                factory.buildProduct(id);
            },
            '4' => {
                try stdout.print("Enter product ID to test: ", .{});
                const id = try stdin.readInt(u32, 10);
                factory.testProduct(id);
            },
            '5' => {
                try stdout.print("Enter product ID to release: ", .{});
                const id = try stdin.readInt(u32, 10);
                factory.releaseProduct(id);
            },
            '6' => {
                try factory.save();
                break;
            },
            else => try stdout.print("Invalid option.\n", .{}),
        }
    }
    
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