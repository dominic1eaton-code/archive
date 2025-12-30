pub const Role = enum {
    Admin,
    User,
};

pub const User = struct {
    username: []const u8,
    password_hash: []const u8,
    role: Role,
};

pub const Vulnerability = struct {
    id: u32,
    description: []const u8,
    severity: []const u8,
};

fn loadUsers(allocator: *std.mem.Allocator) ![]User {
    const file = try std.fs.cwd().openFile("users.json", .{ .read = true });
    defer file.close();
    const data = try file.readToEndAlloc(allocator, 1024);
    defer allocator.free(data);

    var parser = std.json.Parser.init(data);
    const root = try parser.parseRoot();
    const userArray = root.getArray() orelse return error.InvalidFormat;

    var users: []User = &[_]User{};
    for (userArray.items()) |item| {
        const obj = item.getObject() orelse return error.InvalidFormat;
        const username = obj.getString("username") orelse return error.InvalidFormat;
        const password_hash = obj.getString("password_hash") orelse return error.InvalidFormat;
        const role_str = obj.getString("role") orelse return error.InvalidFormat;
        const role = switch (role_str) {
            "Admin" => Role.Admin,
            "User" => Role.User,
            else => return error.InvalidRole,
        };
        var newUsers = try allocator.realloc(users, users.len + 1);
        newUsers[users.len] = User{ .username = username, .password_hash = password_hash, .role = role };
        users = newUsers;
    }
    return users;
}

fn saveUsers(allocator: *std.mem.Allocator, users: []User) !void {
    const file = try std.fs.cwd().createFile("users.json", .{ .write = true, .truncate = true });
    defer file.close();

    try file.writeAll("[\n");
    for (users) |user, index| {
        const role_str = switch (user.role) {
            Role.Admin => "Admin",
            Role.User => "User",
        };
        const line = try std.fmt.allocPrint(allocator, 
            "  {{\"username\":\"{s}\",\"password_hash\":\"{s}\",\"role\":\"{s}\"}}{s}\n", 
            .{ user.username, user.password_hash, role_str, if (index == users.len - 1) "" else "," });
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
            .id = obj.get("id").Int() orelse 0,
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


fn requireAdmin(user: User) !void {
    if (user.role != Role.Admin) {
        return error.PermissionDenied;
    }
}

try requireAdmin(current_user);
vulns = try addVuln(allocator, vulns);

const role_str = obj.get("role").String() orelse "User";
const role = switch (role_str) {
    "Admin" => Role.Admin,
    else => Role.User,
};
users[i] = User{
    .username = username,
    .password_hash = password_hash,
    .role = role,
};

const date_reported = obj.get("date_reported").String() orelse "";
vulns[i] = Vulnerability{
    .id = id,
    .description = desc,
    .severity = sev,
    .date_reported = date_reported,
};