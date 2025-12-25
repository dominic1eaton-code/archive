// vendor management system
const std = @import("std");

const Vendor = struct {
    id: u32,
    name: []u8,
    contact: []u8,
    software: []u8,
    contract_expiry: []u8,

    pub fn free(self: *Vendor, allocator: *std.mem.Allocator) void {
        allocator.free(self.name);
        allocator.free(self.contact);
        allocator.free(self.software);
        allocator.free(self.contract_expiry);
    }
};

pub fn main() !void {
    const allocator = std.heap.page_allocator;
    var vendors: std.ArrayList(Vendor) = std.ArrayList(Vendor).init(allocator);

    // Load existing vendors
    _ = loadVendors(&vendors) catch |err| {
        std.debug.print("No existing vendors found or failed to load: {}\n", .{err});
    };

    const stdout = std.io.getStdOut().writer();
    while (true) {
        try stdout.print(
            "\nVendor Management System\n1. Add Vendor\n2. List Vendors\n3. Search Vendor\n4. Update Vendor\n5. Delete Vendor\n6. Exit\n> ",
            .{},
        );
        var choice: u8 = try readUint8();

        switch (choice) {
            1 => try addVendor(&vendors),
            2 => try listVendors(vendors.items),
            3 => try searchVendor(vendors.items),
            4 => try updateVendor(&vendors),
            5 => try deleteVendor(&vendors),
            6 => {
                try saveVendors(vendors.items);
                // Free all vendor memory
                for (vendors.items) |*v| v.free(allocator);
                break;
            },
            else => try stdout.print("Invalid option.\n", .{}),
        }
    }
}

// ---------------- I/O Functions ----------------

fn readUint8() !u8 {
    var input: [3]u8 = undefined;
    const stdin = std.io.getStdIn().reader();
    const len = try stdin.readUntilDelimiterOrEof(&input, '\n');
    return std.fmt.parseInt(u8, input[0..len], 10);
}

fn readLine(allocator: *std.mem.Allocator) ![]u8 {
    var stdin = std.io.getStdIn().reader();
    var buffer = try allocator.alloc(u8, 64);
    var capacity: usize = 64;
    var len: usize = 0;

    while (true) {
        var byte: u8 = 0;
        const n = try stdin.readByte(&byte);
        if (n == 0 or byte == '\n') break;

        if (len >= capacity) {
            const new_capacity = capacity * 2;
            const new_buffer = try allocator.realloc(buffer, capacity, new_capacity);
            buffer = new_buffer;
            capacity = new_capacity;
        }

        buffer[len] = byte;
        len += 1;
    }

    const result = try allocator.realloc(buffer, capacity, len);
    return result;
}

// ---------------- Vendor Operations ----------------

fn addVendor(vendors: *std.ArrayList(Vendor)) !void {
    const allocator = std.heap.page_allocator;
    const stdout = std.io.getStdOut().writer();
    var v: Vendor = .{0, &[_]u8{}, &[_]u8{}, &[_]u8{}, &[_]u8{}};

    try stdout.print("Enter Vendor ID: ", .{});
    v.id = try readUint8();

    try stdout.print("Enter Name: ", .{});
    v.name = try readLine(allocator);

    try stdout.print("Enter Contact: ", .{});
    v.contact = try readLine(allocator);

    try stdout.print("Enter Software: ", .{});
    v.software = try readLine(allocator);

    try stdout.print("Enter Contract Expiry (YYYY-MM-DD): ", .{});
    v.contract_expiry = try readLine(allocator);

    try vendors.append(v);
    try stdout.print("Vendor added!\n", .{});
}

fn listVendors(vendors: []const Vendor) !void {
    const stdout = std.io.getStdOut().writer();
    if (vendors.len == 0) {
        try stdout.print("No vendors found.\n", .{});
        return;
    }
    for (vendors) |v| {
        try stdout.print(
            "ID: {d}, Name: {s}, Contact: {s}, Software: {s}, Contract Expiry: {s}\n",
            .{v.id, v.name, v.contact, v.software, v.contract_expiry},
        );
    }
}

// ---------------- Case-insensitive partial search ----------------

fn searchVendor(vendors: []const Vendor) !void {
    const allocator = std.heap.page_allocator;
    const stdout = std.io.getStdOut().writer();

    try stdout.print("Enter vendor name to search (partial, case-insensitive): ", .{});
    const query = try readLine(allocator);
    const query_lower = try toLower(allocator, query);

    var found = false;
    for (vendors) |v| {
        const name_lower = try toLower(allocator, v.name);
        if (contains(name_lower, query_lower)) {
            try stdout.print(
                "ID: {d}, Name: {s}, Contact: {s}, Software: {s}, Contract Expiry: {s}\n",
                .{v.id, v.name, v.contact, v.software, v.contract_expiry},
            );
            found = true;
        }
        allocator.free(name_lower);
    }

    if (!found) try stdout.print("Vendor not found.\n", .{});

    allocator.free(query);
    allocator.free(query_lower);
}

// ---------------- Update Function (case-insensitive partial name) ----------------

fn updateVendor(vendors: *std.ArrayList(Vendor)) !void {
    const allocator = std.heap.page_allocator;
    const stdout = std.io.getStdOut().writer();

    try stdout.print("Enter vendor name to update (partial, case-insensitive): ", .{});
    const query = try readLine(allocator);
    const query_lower = try toLower(allocator, query);

    var matches: std.ArrayList(*Vendor) = std.ArrayList(*Vendor).init(allocator);

    for (vendors.items) |*v| {
        const name_lower = try toLower(allocator, v.name);
        if (contains(name_lower, query_lower)) try matches.append(v);
        allocator.free(name_lower);
    }

    if (matches.items.len == 0) {
        try stdout.print("No matching vendor found.\n", .{});
        allocator.free(query);
        allocator.free(query_lower);
        return;
    }

    var target: *Vendor = null;
    if (matches.items.len == 1) {
        target = matches.items[0];
    } else {
        try stdout.print("Multiple vendors found:\n", .{});
        for (matches.items) |v, idx| try stdout.print("{d}. {s}\n", .{idx + 1, v.name});
        try stdout.print("Select vendor number to update: ", .{});
        const sel = try readUint8();
        if (sel == 0 or sel > matches.items.len) {
            try stdout.print("Invalid selection.\n", .{});
            allocator.free(query);
            allocator.free(query_lower);
            matches.deinit();
            return;
        }
        target = matches.items[sel - 1];
    }

    // Partial updates
    try stdout.print("Enter new Name (leave empty to keep current): ", .{});
    const new_name = try readLine(allocator);
    if (new_name.len != 0) { allocator.free(target.name); target.name = new_name; } else allocator.free(new_name);

    try stdout.print("Enter new Contact (leave empty to keep current): ", .{});
    const new_contact = try readLine(allocator);
    if (new_contact.len != 0) { allocator.free(target.contact); target.contact = new_contact; } else allocator.free(new_contact);

    try stdout.print("Enter new Software (leave empty to keep current): ", .{});
    const new_software = try readLine(allocator);
    if (new_software.len != 0) { allocator.free(target.software); target.software = new_software; } else allocator.free(new_software);

    try stdout.print("Enter new Contract Expiry (leave empty to keep current): ", .{});
    const new_expiry = try readLine(allocator);
    if (new_expiry.len != 0) { allocator.free(target.contract_expiry); target.contract_expiry = new_expiry; } else allocator.free(new_expiry);

    try stdout.print("Vendor updated!\n", .{});

    allocator.free(query);
    allocator.free(query_lower);
    matches.deinit();
}

// ---------------- Delete Function (case-insensitive partial name) ----------------

fn deleteVendor(vendors: *std.ArrayList(Vendor)) !void {
    const allocator = std.heap.page_allocator;
    const stdout = std.io.getStdOut().writer();

    try stdout.print("Enter vendor name to delete (partial, case-insensitive): ", .{});
    const query = try readLine(allocator);
    const query_lower = try toLower(allocator, query);

    var matches: std.ArrayList(usize) = std.ArrayList(usize).init(allocator);

    for (vendors.items) |v, idx| {
        const name_lower = try toLower(allocator, v.name);
        if (contains(name_lower, query_lower)) try matches.append(idx);
        allocator.free(name_lower);
    }

    if (matches.items.len == 0) {
        try stdout.print("No matching vendor found.\n", .{});
        allocator.free(query);
        allocator.free(query_lower);
        matches.deinit();
        return;
    }

    var indices_to_delete: std.ArrayList(usize) = std.ArrayList(usize).init(allocator);

    if (matches.items.len == 1) {
        try indices_to_delete.append(matches.items[0]);
    } else {
        try stdout.print("Multiple vendors found:\n", .{});
        for (matches.items) |idx, i| {
            const v = vendors.items[idx];
            try stdout.print("{d}. {s}\n", .{i + 1, v.name});
        }
        try stdout.print("Enter comma-separated numbers of vendors to delete (e.g., 1,3): ", .{});
        var input_line = try readLine(allocator);
        const parts = std.mem.split(input_line, ",");
        for (parts) |part| {
            const sel = try std.fmt.parseInt(usize, part, 10);
            if (sel == 0 or sel > matches.items.len) { try stdout.print("Invalid selection: {s}\n", .{part}); continue; }
            try indices_to_delete.append(matches.items[sel - 1]);
        }
        allocator.free(input_line);
    }

    // Delete in reverse order
    std.sort.reverse(indices_to_delete.items);
    for (indices_to_delete.items) |idx| {
        vendors.items[idx].free(allocator);
        _ = vendors.items.swapRemove(idx);
    }

    try stdout.print("Selected vendor(s) deleted!\n", .{});

    allocator.free(query);
    allocator.free(query_lower);
    matches.deinit();
    indices_to_delete.deinit();
}

// ---------------- JSON Persistence ----------------

fn saveVendors(vendors: []const Vendor) !void {
    const stdout = std.io.getStdOut().writer();
    const file = try std.fs.cwd().createFile("vendors.json", .{ .truncate = true });
    defer file.close();

    const json_writer = std.json.StreamWriter.init(file.writer());
    try json_writer.beginArray();
    for (vendors) |v, idx| {
        try json_writer.beginObject();
        try json_writer.writeKeyValue("id", v.id);
        try json_writer.writeKeyValue("name", v.name);
        try json_writer.writeKeyValue("contact", v.contact);
        try json_writer.writeKeyValue("software", v.software);
        try json_writer.writeKeyValue("contract_expiry", v.contract_expiry);
        try json_writer.endObject(idx != vendors.len - 1);
    }
    try json_writer.endArray();
    try stdout.print("Vendors saved to vendors.json\n", .{});
}

fn loadVendors(vendors: *std.ArrayList(Vendor)) !void {
    const allocator = std.heap.page_allocator;
    const file = try std.fs.cwd().openFile("vendors.json", .{});
    defer file.close();

    const file_data = try file.readToEndAlloc(allocator, 8192);
    defer allocator.free(file_data);

    var parser = std.json.Parser.init(file_data);
    const root = try parser.parseRoot();
    if (root.getType() != .Array) return;

    const arr = root.Array();
    for (arr.items) |item| {
        var v: Vendor = .{0, &[_]u8{}, &[_]u8{}, &[_]u8{}, &[_]u8{}};
        v.id = item.Object().?["id"].Int() catch continue;
        v.name = try copyString(allocator, item.Object().?["name"].String() orelse "");
        v.contact = try copyString(allocator, item.Object().?["contact"].String() orelse "");
        v.software = try copyString(allocator, item.Object().?["software"].String() orelse "");
        v.contract_expiry = try copyString(allocator, item.Object().?["contract_expiry"].String() orelse "");
        try vendors.append(v);
    }
}

fn copyString(allocator: *std.mem.Allocator, s: []const u8) ![]u8 {
    const buf = try allocator.alloc(u8, s.len);
    std.mem.copy(u8, buf, s);
    return buf;
}

// ---------------- String Helpers ----------------

fn toLower(allocator: *std.mem.Allocator, s: []const u8) ![]u8 {
    const buf = try allocator.alloc(u8, s.len);
    for (s) |c, i| {
        if (c >= 'A' and c <= 'Z') buf[i] = c + 32;
        else buf[i] = c;
    }
    return buf;
}

fn contains(haystack: []const u8, needle: []const u8) bool {
    if (needle.len == 0 or haystack.len < needle.len) return false;
    for (haystack.len - needle.len + 1) |i| {
        if (std.mem.eql(u8, haystack[i..i+needle.len], needle)) return true;
    }
    return false;
}
