// application security management system
// security_manager.zig
// A simple CLI security management system in Zig.
// - Users stored with Argon2-hashed passwords (PHC encoding).
// - Vulnerabilities stored in JSON.
// - Append-only "chain-hash" log for tamper detection.
// - CLI commands: adduser, auth, listusers, addvuln, listvulns, exit.

const std = @import("std");
const json = std.json;
const pwhash = std.crypto.pwhash.argon2;
const hash = std.crypto.hash;

const USER_FILE = "users.json";
const VULN_FILE = "vulns.json";
const LOG_FILE  = "logs.txt";

const Allocator = std.mem.Allocator;

pub const User = struct {
    username: []const u8,
    password_hash: []const u8, // PHC‑encoded Argon2 hash
};

pub const Vulnerability = struct {
    id: u32,
    description: []const u8,
    severity: []const u8,
};

// --- Utility: read a line from stdin ---
fn prompt(allocator: *Allocator, prompt_msg: []const u8) ![]u8 {
    try std.debug.print("{s}: ", .{prompt_msg});
    var line = try std.io.getStdIn().readLineAlloc(allocator, 1024);
    // strip trailing newline if present
    if (line.len > 0 and line[line.len-1] == '\n') {
        _ = line[0..line.len-1];
    }
    return line;
}

// --- Password hashing and verification ---
fn hashPassword(allocator: *Allocator, password: []const u8) ![]u8 {
    return try pwhash.strHash(
        password,
        pwhash.HashOptions{
            .allocator = allocator,
            .params = .{},         // default (safe) parameters
            .encoding = .phc,
        }
    );
}

fn verifyPassword(stored_hash: []const u8, password: []const u8) !bool {
    return try pwhash.strVerify(
        stored_hash,
        password,
        pwhash.VerifyOptions{ .allocator = std.heap.page_allocator },
    );
}

// --- Chain-hash logging ---
var prev_log_hash: [32]u8 = undefined;

fn initLog() !void {
    if (!std.fs.cwd().exists(LOG_FILE)) {
        // first-time: initialize with zero-hash
        for (prev_log_hash.*) |*b| { b.* = 0; }
    } else {
        const file = try std.fs.cwd().openFile(LOG_FILE, .{});
        defer file.close();
        const data = try file.readToEndAlloc(std.heap.page_allocator, 8192);
        defer std.heap.page_allocator.free(data);

        // find last line
        const lines = std.mem.split(data, "\n", false);
        if (lines.len > 0) {
            const last = lines[lines.len - 1];
            // expect format: "<timestamp> - <action> || <hexhash>"
            const parts = std.mem.split(last, "||", false);
            if (parts.len == 2) {
                const hex = std.mem.trim(parts[1], " \r\n");
                _ = try std.fmt.hexToBytes(prev_log_hash[0..], hex, .lower);
            } else {
                // malformed, treat as zero-hash
                for (prev_log_hash.*) |*b| { b.* = 0; }
            }
        } else {
            for (prev_log_hash.*) |*b| { b.* = 0; }
        }
    }
}

fn logAction(action: []const u8) !void {
    const ts = try std.time.now().format(.RFC3339, std.time.Zone.utc, std.heap.page_allocator);
    defer std.heap.page_allocator.free(ts);

    const entry = try std.fmt.allocPrint(std.heap.page_allocator, "{s} - {s}", .{ts, action});
    defer std.heap.page_allocator.free(entry);

    const to_hash_len = entry.len + prev_log_hash.len;
    var to_hash = try std.heap.page_allocator.alloc(u8, to_hash_len);
    defer std.heap.page_allocator.free(to_hash);
    std.mem.copy(u8, to_hash[0..entry.len], entry);
    std.mem.copy(u8, to_hash[entry.len..], prev_log_hash[0..]);

    const new_hash = hash.sha256(to_hash);

    const file = try std.fs.cwd().openFileAppend(LOG_FILE, .{});
    defer file.close();
    try file.writeAll(entry);
    try file.writeAll(" || ");
    try file.writeAll(std.fmt.bytesToHex(new_hash, .lower));
    try file.writeAll("\n");

    prev_log_hash = new_hash;
}

// --- JSON load/save for Users ---
fn loadUsers(allocator: *Allocator) ![]User {
    if (!std.fs.cwd().exists(USER_FILE)) {
        return &[_]User{}; // empty slice
    }
    const file = try std.fs.cwd().openFile(USER_FILE, .{});
    defer file.close();
    const data = try file.readToEndAlloc(allocator, 8192);
    defer allocator.free(data);

    var parser = json.Parser.init(data);
    const root = try parser.parseRoot();
    if (root.getType() != .Array) return &[_]User{};
    const arr = root.Array() orelse return &[_]User{};

    var users = try allocator.alloc(User, arr.len);
    for (arr.items()) |item, i| {
        const obj = item.Object() orelse continue;
        const u = obj.get("username").String() orelse "";
        const ph = obj.get("password_hash").String() orelse "";
        users[i] = User{
            .username = u,
            .password_hash = ph,
        };
    }
    return users;
}

fn saveUsers(allocator: *Allocator, users: []User) !void {
    const file = try std.fs.cwd().createFile(USER_FILE, .{});
    defer file.close();
    try file.writeAll("[\n");
    for (users) |u, idx| {
        const comma = if (idx == users.len - 1) "" else ",";
        const line = try std.fmt.allocPrint(allocator,
            "  {{\"username\": \"{s}\", \"password_hash\": \"{s}\"}}{s}\n",
            .{u.username, u.password_hash, comma});
        defer allocator.free(line);
        try file.writeAll(line);
    }
    try file.writeAll("]\n");
}

// --- JSON load/save for Vulnerabilities ---
fn loadVulns(allocator: *Allocator) ![]Vulnerability {
    if (!std.fs.cwd().exists(VULN_FILE)) {
        return &[_]Vulnerability{};
    }
    const file = try std.fs.cwd().openFile(VULN_FILE, .{});
    defer file.close();
    const data = try file.readToEndAlloc(allocator, 8192);
    defer allocator.free(data);

    var parser = json.Parser.init(data);
    const root = try parser.parseRoot();
    if (root.getType() != .Array) return &[_]Vulnerability{};
    const arr = root.Array() orelse return &[_]Vulnerability{};

    var vulns = try allocator.alloc(Vulnerability, arr.len);
    for (arr.items()) |item, i| {
        const obj = item.Object() orelse continue;
        const id = @intCast(u32, obj.get("id").Integer() orelse 0);
        const desc = obj.get("description").String() orelse "";
        const sev  = obj.get("severity").String() orelse "";
        vulns[i] = Vulnerability{ .id = id, .description = desc, .severity = sev };
    }
    return vulns;
}

fn saveVulns(allocator: *Allocator, vulns: []Vulnerability) !void {
    const file = try std.fs.cwd().createFile(VULN_FILE, .{});
    defer file.close();
    try file.writeAll("[\n");
    for (vulns) |v, idx| {
        const comma = if (idx == vulns.len - 1) "" else ",";
        const line = try std.fmt.allocPrint(allocator,
            "  {{\"id\": {d}, \"description\": \"{s}\", \"severity\": \"{s}\"}}{s}\n",
            .{v.id, v.description, v.severity, comma});
        defer allocator.free(line);
        try file.writeAll(line);
    }
    try file.writeAll("]\n");
}

// --- CLI command implementations ---
fn addUser(allocator: *Allocator, users: []User) ![]User {
    const username = try prompt(allocator, "Enter new username");
    const password = try prompt(allocator, "Enter password");
    const hashed = try hashPassword(allocator, password);

    // check for existing username
    for (users) |u| {
        if (std.mem.eql(u8, u.username, username)) {
            std.debug.print("User {s} already exists.\n", .{username});
            return users;
        }
    }

    var new_users = try allocator.alloc(User, users.len + 1);
    std.mem.copy(User, new_users[0..users.len], users);
    new_users[users.len] = User{ .username = username, .password_hash = hashed };

    try saveUsers(allocator, new_users);
    try logAction("Added user " ++ new_users[users.len].username);

    return new_users;
}

fn authenticateUser(users: []User) !void {
    const username = try prompt(std.heap.page_allocator, "Username");
    const password = try prompt(std.heap.page_allocator, "Password");
    for (users) |u| {
        if (std.mem.eql(u8, u.username, username)) {
            if (try verifyPassword(u.password_hash, password)) {
                std.debug.print("Authentication succeeded.\n", .{});
                try logAction("Authenticated user " ++ username);
                return;
            } else {
                std.debug.print("Incorrect password.\n", .{});
                try logAction("Failed authentication attempt for user " ++ username);
                return;
            }
        }
    }
    std.debug.print("User not found.\n", .{});
    try logAction("Failed authentication (user not found): " ++ username);
}

fn listUsers(users: []User) void {
    std.debug.print("Users:\n", .{});
    for (users) |u| {
        std.debug.print(" - {s}\n", .{u.username});
    }
}

fn addVuln(allocator: *Allocator, vulns: []Vulnerability) ![]Vulnerability {
    const desc = try prompt(allocator, "Vuln description");
    const sev  = try prompt(allocator, "Severity");
    const next_id = if (vulns.len == 0) 1 else vulns[vulns.len-1].id + 1;

    var new_vulns = try allocator.alloc(Vulnerability, vulns.len + 1);
    std.mem.copy(Vulnerability, new_vulns[0..vulns.len], vulns);
    new_vulns[vulns.len] = Vulnerability{ .id = next_id, .description = desc, .severity = sev };

    try saveVulns(allocator, new_vulns);
    try logAction("Added vulnerability id=" ++ std.fmt.allocPrint(
        allocator, "{d}", .{next_id}) orelse "unknown");

    return new_vulns;
}

fn listVulns(vulns: []Vulnerability) void {
    std.debug.print("Vulnerabilities:\n", .{});
    for (vulns) |v| {
        std.debug.print(" - [{d}] {s} (Severity: {s})\n", .{v.id, v.description, v.severity});
    }
}

// --- Main CLI loop ---
pub fn main() !void {
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    const allocator = &gpa.allocator;

    try initLog();

    var users = try loadUsers(allocator);
    var vulns = try loadVulns(allocator);

    while (true) {
        std.debug.print(
            "\nCommands: adduser, auth, listusers, addvuln, listvulns, exit\n> ", .{});
        const cmd_raw = try std.io.getStdIn().readLineAlloc(allocator, 64);
        defer allocator.free(cmd_raw);

        const cmd = std.mem.trim(cmd_raw, " \r\n");
        if (std.mem.eql(u8, cmd, "adduser")) {
            users = try addUser(allocator, users);
        } else if (std.mem.eql(u8, cmd, "auth")) {
            try authenticateUser(users);
        } else if (std.mem.eql(u8, cmd, "listusers")) {
            listUsers(users);
        } else if (std.mem.eql(u8, cmd, "addvuln")) {
            vulns = try addVuln(allocator, vulns);
        } else if (std.mem.eql(u8, cmd, "listvulns")) {
            listVulns(vulns);
        } else if (std.mem.eql(u8, cmd, "exit")) {
            break;
        } else {
            std.debug.print("Unknown command: {s}\n", .{cmd});
        }
    }
}
