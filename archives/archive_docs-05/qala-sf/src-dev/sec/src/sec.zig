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
    const desc = try prompt(allocator, "Enter vulnerability description");
    const sev = try prompt(allocator, "Enter severity");
    var newVulns = try allocator.realloc(vulns, vulns.len + 1);
    const nextId = if (vulns.len == 0) 1 else vulns[vulns.len-1].id + 1;
    newVulns[vulns.len] = Vulnerability{ .id = nextId, .description = desc, .severity = sev };
    try saveVulns(allocator, newVulns);
    try logAction("Added vulnerability " ++ desc);
}

fn listVulns(vulns: []Vulnerability) void {
    std.debug.print("Vulnerabilities:\n", .{});
    for (vulns) |v| {
        std.debug.print(" - [{d}] {s} (Severity: {s})\n", .{v.id, v.description, v.severity});
    }
}

// --- Main CLI Loop ---

pub fn main() !void {
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    const allocator = &gpa.allocator;

    var users = try loadUsers(allocator);
    var vulns = try loadVulns(allocator);

    while (true) {
        std.debug.print("\nCommands: adduser, listusers, addvuln, listvulns, exit\n> ", .{});
        var input = try std.io.getStdIn().readLineAlloc(allocator, 64);
        defer allocator.free(input);

        if (std.mem.eql(u8, input, "adduser")) {
            try addUser(allocator, users);
            users = try loadUsers(allocator);
        } else if (std.mem.eql(u8, input, "listusers")) {
            listUsers(users);
        } else if (std.mem.eql(u8, input, "addvuln")) {
            try addVuln(allocator, vulns);
            vulns = try loadVulns(allocator);
        } else if (std.mem.eql(u8, input, "listvulns")) {
            listVulns(vulns);
        } else if (std.mem.eql(u8, input, "exit")) {
            break;
        } else {
            std.debug.print("Unknown command.\n", .{});
        }
    }

        std.debug.print("\nCommands: adduser, listusers, addvuln, listvulns, exit\n> ", .{});
        var input = try std.io.getStdIn().readLineAlloc(allocator, 64);
        defer allocator.free(input);

        if (std.mem.eql(u8, input, "adduser")) {
            try addUser(allocator, users);
            users = try loadUsers(allocator);
        } else if (std.mem.eql(u8, input, "listusers")) {
            listUsers(users);
        } else if (std.mem.eql(u8, input, "addvuln")) {
            try addVuln(allocator, vulns);
            vulns = try loadVulns(allocator);
        } else if (std.mem.eql(u8, input, "listvulns")) {
            listVulns(vulns);
        } else if (std.mem.eql(u8, input, "exit")) {
            break;
        } else {
            std.debug.print("Unknown command.\n", .{});
        }
    }
}

fn computeFileHash(path: []const u8, allocator: *Allocator) ![32]u8 {
    const file = try std.fs.cwd().openFile(path, .{});
    defer file.close();
    const data = try file.readToEndAlloc(allocator, 8192);
    defer allocator.free(data);
    return hash.sha256(data);
}

fn saveFileHash(path: []const u8, digest: [32]u8) !void {
    const file = try std.fs.cwd().createFile(path, .{});
    defer file.close();
    try file.writeAll(std.fmt.bytesToHex(digest, .lower));
}