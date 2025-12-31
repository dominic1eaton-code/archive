const std = @import("std");
const json = std.json;

const User = struct {
    username: []const u8,
    password: []const u8, // plaintext for simplicity, should hash in real use
};

const Vulnerability = struct {
    id: u32,
    description: []const u8,
    severity: []const u8,
};

// --- Utility Functions ---

fn nowTimestamp() []const u8 {
    const gpa = std.heap.page_allocator;
    var buffer: [64]u8 = undefined;
    const time = std.time.milliTimestamp();
    const s = try std.fmt.bufPrint(&buffer, "{d}", .{time});
    return s;
}

fn logAction(action: []const u8) !void {
    const file = try std.fs.cwd().openFileAppend("logs.txt", .{});
    defer file.close();
    try file.writeAll(nowTimestamp());
    try file.writeAll(" - ");
    try file.writeAll(action);
    try file.writeAll("\n");
}

// --- JSON Storage Functions ---

fn loadUsers(allocator: *std.mem.Allocator) ![]User {
    const path = "users.json";
    if (!std.fs.cwd().exists(path)) return &[_]User{}; // empty array if file missing
    const file = try std.fs.cwd().openFile(path, .{});
    defer file.close();
    const data = try file.readToEndAlloc(allocator, 4096);
    defer allocator.free(data);

    var parser = json.Parser.init(data);
    const root = try parser.parseRoot();
    if (root.getType() != .Array) return &[_]User{};
    var arr = root.Array() orelse return &[_]User{};

    var users = try allocator.alloc(User, arr.len);
    for (arr.items()) |item, i| {
        const obj = item.Object() orelse continue;
        users[i] = User{
            .username = obj.get("username").String() orelse "",
            .password = obj.get("password").String() orelse "",
        };
    }
    return users;
}

fn saveUsers(allocator: *std.mem.Allocator, users: []User) !void {
    const file = try std.fs.cwd().createFile("users.json", .{});
    defer file.close();
    try file.writeAll("[\n");
    for (users) |u, i| {
        const line = try std.fmt.allocPrint(allocator, "  {{\"username\":\"{s}\",\"password\":\"{s}\"}}{s}\n", .{u.username, u.password, if (i == users.len-1) "" else ","});
        defer allocator.free(line);
        try file.writeAll(line);
    }
    try file.writeAll("]\n");
}

fn loadVulns(allocator: *std.mem.Allocator) ![]Vulnerability {
    const path = "vulns.json";
    if (!std.fs.cwd().exists(path)) return &[_]Vulnerability{};
    const file = try std.fs.cwd().openFile(path, .{});
    defer file.close();
    const data = try file.readToEndAlloc(allocator, 4096);
    defer allocator.free(data);

    var parser = json.Parser.init(data);
    const root = try parser.parseRoot();
    if (root.getType() != .Array) return &[_]Vulnerability{};
    var arr = root.Array() orelse return &[_]Vulnerability{};

    var vulns = try allocator.alloc(Vulnerability, arr.len);
    for (arr.items()) |item, i| {
        const obj = item.Object() orelse continue;
        vulns[i] = Vulnerability{
            .id = obj.get("id").Integer() orelse 0,
            .description = obj.get("description").String() orelse "",
            .severity = obj.get("severity").String() orelse "",
        };
    }
    return vulns;
}

fn saveVulns(allocator: *std.mem.Allocator, vulns: []Vulnerability) !void {
    const file = try std.fs.cwd().createFile("vulns.json", .{});
    defer file.close();
    try file.writeAll("[\n");
    for (vulns) |v, i| {
        const line = try std.fmt.allocPrint(allocator, "  {{\"id\":{d},\"description\":\"{s}\",\"severity\":\"{s}\"}}{s}\n", .{v.id, v.description, v.severity, if (i == vulns.len-1) "" else ","});
        defer allocator.free(line);
        try file.writeAll(line);
    }
    try file.writeAll("]\n");
}

// --- CLI Functions ---

fn prompt(allocator: *std.mem.Allocator, msg: []const u8) ![]u8 {
    std.debug.print("{s}: ", .{msg});
    var line = try std.io.getStdIn().readLineAlloc(allocator, 256);
    return line;
}

fn addUser(allocator: *std.mem.Allocator, users: []User) !void {
    const username = try prompt(allocator, "Enter username");
    const password = try prompt(allocator, "Enter password");
    var newUsers = try allocator.realloc(users, users.len + 1);
    newUsers[users.len] = User{ .username = username, .password = password };
    try saveUsers(allocator, newUsers);
    try logAction("Added user " ++ username);
}

fn listUsers(users: []User) void {
    std.debug.print("Users:\n", .{});
    for (users) |u| {
        std.debug.print(" - {s}\n", .{u.username});
    }
}

fn addVuln(allocator: *std.mem.Allocator, vulns: []Vulnerability) !void {
    const description = try prompt(allocator, "Enter vulnerability description");
    const severity = try prompt(allocator, "Enter severity (low/medium/high)");
    var newVulns = try allocator.realloc(vulns, vulns.len + 1);
    newVulns[vulns.len] = Vulnerability{ .id = @intCast(u32, vulns.len + 1), .description = description, .severity = severity };
    try saveVulns(allocator, newVulns);
    try logAction("Added vulnerability " ++ description);
}

fn listVulns(vulns: []Vulnerability) void {
    std.debug.print("Vulnerabilities:\n", .{});
    for (vulns) |v| {
        std.debug.print(" - ID: {d}, Desc: {s}, Severity: {s}\n", .{v.id, v.description, v.severity});
    }
}

// --- Main Function ---
pub fn main() !void {
    const allocator = std.heap.page_allocator;

    var users = try loadUsers(allocator);
    var vulns = try loadVulns(allocator);

    while (true) {
        std.debug.print("\nMenu:\n1. Add User\n2. List Users\n3. Add Vulnerability\n4. List Vulnerabilities\n5. Exit\nChoose an option: ", .{});
        const choice_line = try std.io.getStdIn().readLineAlloc(allocator, 16);
        defer allocator.free(choice_line);
        const choice = std.fmt.parseInt(u8, choice_line, 10) orelse 0;

        switch (choice) {
            1 => try addUser(allocator, users),
            2 => listUsers(users),
            3 => try addVuln(allocator, vulns),
            4 => listVulns(vulns),
            5 => break,
            else => std.debug.print("Invalid choice.\n", .{}),
        }
    }
}

const std = @import("std");
const pwhash = std.crypto.pwhash.argon2;
const hash = std.crypto.hash;

const User = struct {
    username: []const u8,
    password_hash: []const u8, // PHC‑encoded Argon2 hash
};

// For logs: we keep track of last hash in memory
var prev_log_hash: [32]u8 = undefined;

fn initLog() !void {
    if (!std.fs.cwd().exists("logs.txt")) {
        // initialize chain with zero hash
        prev_log_hash = [_]u8{0} ** 32;
    } else {
        // read last line, parse its hash to set prev_log_hash
        const file = try std.fs.cwd().openFile("logs.txt", .{});
        defer file.close();
        var it = try file.readToEndAlloc(std.heap.page_allocator, 8192);
        defer std.heap.page_allocator.free(it);
        // parse last line after “||” to get last hash (hex)
        // convert hex to bytes into prev_log_hash
        // (omitted for brevity)
    }
}

fn logAction(action: []const u8) !void {
    const timestamp = try std.time.now().format(
        .RFC3339, std.time.Zone.utc,
        std.heap.page_allocator
    );
    defer std.heap.page_allocator.free(timestamp);

    const entry = try std.fmt.allocPrint(std.heap.page_allocator,
        "{s} - {s}", .{timestamp, action});
    defer std.heap.page_allocator.free(entry);

    var to_hash = std.heap.page_allocator.alloc(u8, entry.len + prev_log_hash.len) catch unreachable;
    defer std.heap.page_allocator.free(to_hash);
    std.mem.copy(u8, to_hash[0..entry.len], entry);
    std.mem.copy(u8, to_hash[entry.len..], prev_log_hash[0..]);

    const new_hash = hash.sha256(to_hash);

    const file = try std.fs.cwd().openFileAppend("logs.txt", .{});
    defer file.close();
    try file.writeAll(entry);
    try file.writeAll(" || ");
    try file.writeAll(std.fmt.bytesToHex(new_hash, .lower));
    try file.writeAll("\n");

    prev_log_hash = new_hash;
}

// Example user creation:
fn addUser(...) !void {
    const username = ...
    const password = ...
    const password_hash = try hashPassword(allocator, password);
    // store username + password_hash in user JSON
    ...
    try logAction("Added user " ++ username);
}