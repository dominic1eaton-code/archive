const std = @import("std");
const json = std.json;

pub const Config = struct {
    data: json.Value,

    pub fn load(path: []const u8, allocator: *std.mem.Allocator) !Config {
        var file = try std.fs.cwd().openFile(path, .{ .read = true });
        defer file.close();

        const file_size = try file.getEndPos();
        var buffer = try allocator.alloc(u8, file_size);
        defer allocator.free(buffer);

        _ = try file.readAll(buffer);

        const parser = json.Parser.init(buffer);
        const value = try parser.parse();
        return Config{ .data = value };
    }

    pub fn getString(self: *Config, key: []const u8) ?[]const u8 {
        const val = self.data.Object.get(key);
        if (val) |v| switch (v) {
            .String => return v.String,
            else => return null,
        } else return null;
    }

    pub fn getInt(self: *Config, key: []const u8) ?i64 {
        const val = self.data.Object.get(key);
        if (val) |v| switch (v) {
            .Int => return v.Int,
            else => return null,
        } else return null;
    }

    pub fn getBool(self: *Config, key: []const u8) ?bool {
        const val = self.data.Object.get(key);
        if (val) |v| switch (v) {
            .Bool => return v.Bool,
            else => return null,
        } else return null;
    }
};

const std = @import("std");
const Config = @import("config").Config;

pub fn main() !void {
    const allocator = std.heap.page_allocator;

    const config = try Config.load("config.json", allocator);

    const app_name = config.getString("app_name") orelse "Unknown";
    const version = config.getString("version") orelse "0.0.0";
    const debug = config.getBool("debug") orelse false;
    const max_connections = config.getInt("max_connections") orelse 0;

    std.debug.print("App: {s}, Version: {s}\n", .{ app_name, version });
    std.debug.print("Debug: {b}, Max Connections: {d}\n", .{ debug, max_connections });
}

const std = @import("std");
const json = std.json;

pub const Config = struct {
    data: json.Value,
    path: []const u8,

    pub fn saveTOML(self: *Config) !void {
        var file = try std.fs.cwd().createFile(self.path, .{ .truncate = true });
        defer file.close();

        const writer = file.writer();
        try serializeTOML(self.data, writer);
    }

    pub fn loadTOML(path: []const u8, allocator: *std.mem.Allocator) !Config {
        var file = try std.fs.cwd().openFile(path, .{ .read = true });
        defer file.close();

        const size = try file.getEndPos();
        var buffer = try allocator.alloc(u8, size);
        defer allocator.free(buffer);
        _ = try file.readAll(buffer);

        const data = try parseTOML(allocator, buffer);
        return Config{ .data = data, .path = path };
    }

    pub fn load(path: []const u8, allocator: *std.mem.Allocator) !Config {
        var file = try std.fs.cwd().openFile(path, .{ .read = true });
        defer file.close();

        const file_size = try file.getEndPos();
        var buffer = try allocator.alloc(u8, file_size);
        defer allocator.free(buffer);

        _ = try file.readAll(buffer);

        const parser = json.Parser.init(buffer);
        const value = try parser.parse();
        return Config{ .data = value, .path = path };
    }

    fn traverseNested(self: *Config, key: []const u8) ?*json.Value {
        const allocator = std.heap.page_allocator;
        var segments_it = std.mem.split(key, ".");

        var current: *json.Value = &self.data;
        while (segments_it.next()) |segment| {
            if (current.*.tag != .Object) return null;
            const obj = current.Object;
            current = obj.get(segment) orelse return null;
        }
        return current;
    }

    pub fn getString(self: *Config, key: []const u8) ?[]const u8 {
        const val = self.traverseNested(key);
        if (val) |v| switch (v.*.tag) {
            .String => return v.String,
            else => return null,
        } else return null;
    }

    pub fn getInt(self: *Config, key: []const u8) ?i64 {
        const val = self.traverseNested(key);
        if (val) |v| switch (v.*.tag) {
            .Int => return v.Int,
            else => return null,
        } else return null;
    }

    pub fn getBool(self: *Config, key: []const u8) ?bool {
        const val = self.traverseNested(key);
        if (val) |v| switch (v.*.tag) {
            .Bool => return v.Bool,
            else => return null,
        } else return null;
    }

    pub fn setString(self: *Config, key: []const u8, value: []const u8) !void {
        const allocator = std.heap.page_allocator;
        var segments_it = std.mem.split(key, ".");

        var current: *json.Value = &self.data;
        var last_segment: []const u8 = "";
        while (segments_it.next()) |segment| {
            if (segments_it.peek() == null) last_segment = segment;

            if (current.*.tag != .Object) return error.InvalidPath;
            var obj = current.Object;
            var next = obj.get(segment);
            if (next == null) {
                // create intermediate object if missing
                const new_obj = json.Value.initObject(allocator) catch return error.AllocFailed;
                _ = try obj.put(segment, new_obj);
            }
            current = obj.get(segment) orelse unreachable;
        }

        // set final string
        current.Object.put(last_segment, json.Value{ .String = value });
    }

    pub fn saveJSON(self: *Config) !void {
        var file = try std.fs.cwd().createFile(self.path, .{ .truncate = true });
        defer file.close();
        const writer = std.io.fixedBufferStream(file);
        try json.print(&writer.writer(), self.data);
    }
};

pub fn parseSimpleTOML(allocator: *std.mem.Allocator, text: []const u8) !json.Value {
    var obj = json.Value.initObject(allocator) catch return error.AllocFailed;
    var current: *json.Value = &obj;
    var current_table: []const u8 = "";

    const lines = std.mem.split(text, "\n");
    for (lines) |line| {
        const ltrim = std.mem.trimLeft(line, " \t");
        if (ltrim.len == 0 or ltrim[0] == '#') continue;

        if (ltrim[0] == '[' and ltrim[ltrim.len - 1] == ']') {
            // new table
            current_table = ltrim[1 .. ltrim.len - 1];
            const new_obj = json.Value.initObject(allocator) catch return error.AllocFailed;
            try obj.Object.put(current_table, new_obj);
            current = obj.Object.get(current_table) orelse unreachable;
            continue;
        }

        // key = value
        const kv = std.mem.split(ltrim, "=");
        const key = std.mem.trim(kv.next() orelse return error.InvalidTOML, " \t");
        const value_raw = std.mem.trim(kv.next() orelse return error.InvalidTOML, " \t");

        if (std.mem.startsWith(value_raw, "\"") and std.mem.endsWith(value_raw, "\"")) {
            try current.Object.put(key, json.Value{ .String = value_raw[1 .. value_raw.len - 1] });
        } else if (std.fmt.parseInt(i64, value_raw, 10)) |v| {
            try current.Object.put(key, json.Value{ .Int = v });
        } else if (std.mem.eql(u8, value_raw, "true")) {
            try current.Object.put(key, json.Value{ .Bool = true });
        } else if (std.mem.eql(u8, value_raw, "false")) {
            try current.Object.put(key, json.Value{ .Bool = false });
        }
    }

    return obj;
}

const std = @import("std");
const Config = @import("config").Config;

pub fn main() !void {
    const allocator = std.heap.page_allocator;

    // Load JSON
    var config = try Config.load("config.json", allocator);

    // Nested key
    const db_host = config.getString("database.host") orelse "127.0.0.1";
    std.debug.print("DB Host: {s}\n", .{db_host});

    // Modify value
    try config.setString("database.host", "192.168.1.100");
    try config.saveJSON();
}
// const std = @import("std");
// const Config = @import("config").Config;
// const parseSimpleTOML = @import("config").parseSimpleTOML;

pub fn main() !void {
    const allocator = std.heap.page_allocator;

    var config = try Config.load("config.toml", allocator);

    // Read nested keys
    const db_host = config.getString("database.host") orelse "localhost";
    std.debug.print("DB Host: {s}\n", .{db_host});

    // Modify value
    try config.setString("database.host", "192.168.1.50");

    // Save as TOML
    try config.saveTOML();
}
