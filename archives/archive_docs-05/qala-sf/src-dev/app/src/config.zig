const std = @import("std");

pub const Config = struct {
    allocator: *std.mem.Allocator,

    pub fn loadProjectConfig(allocator: *std.mem.Allocator) !?std.StringHashMap([]const u8) {
        var dir = try std.fs.cwd().openDir(".");
        defer dir.close();
        while (true) {
            const config_path = try std.fmt.allocPrint(allocator, "{s}/.envmgr", .{dir.path});
            if (try std.fs.cwd().exists(config_path)) {
                return try parseConfigFile(allocator, config_path);
            }
            if (dir.path == "/") break;
            dir.path = std.fs.pathDir(dir.path);
        }
        return null;
    }

    fn parseConfigFile(allocator: *std.mem.Allocator, path: []const u8) !std.StringHashMap([]const u8) {
        var file = try std.fs.cwd().openFile(path, .{ .read = true });
        defer file.close();

        var map = std.StringHashMap([]const u8).init(allocator);
        var reader = file.reader();
        var line = try reader.readUntilDelimiterOrEof(allocator, '\n');
        while (line) |l| {
            const idx = std.mem.indexOf(u8, l, '=');
            if (idx) |i| {
                const key = l[0..i];
                const value = l[i + 1 ..];
                _ = try map.put(key, value);
            }
            line = try reader.readUntilDelimiterOrEof(allocator, '\n');
        }
        return map;
    }

    pub fn saveLockfile(allocator: *std.mem.Allocator, path: []const u8, map: std.StringHashMap([]const u8)) !void {
        var file = try std.fs.cwd().createFile(path, .{});
        defer file.close();

        try file.writeAll("{\n");
        var it = map.iterator();
        while (it.next()) |entry| {
            try file.writeAll(std.fmt.allocPrint(allocator, "  \"{s}\": \"{s}\"", .{ entry.key_ptr.*, entry.value_ptr.* }));
            if (it.hasNext()) try file.writeAll(",\n");
        }
        try file.writeAll("\n}\n");
    }

    pub fn loadLockfile(allocator: *std.mem.Allocator, path: []const u8) !?std.StringHashMap([]const u8) {
        if (!try std.fs.cwd().exists(path)) return null;
        // Simple JSON parsing for lockfile
        var file = try std.fs.cwd().openFile(path, .{ .read = true });
        defer file.close();

        var map = std.StringHashMap([]const u8).init(allocator);
        var reader = file.reader();
        var buf: [1024]u8 = undefined;
        const bytes = try reader.readAll(&buf);
        var str = buf[0..bytes];
        while (str.len > 0) {
            const quote1 = std.mem.indexOf(u8, str, '"') orelse break;
            str = str[quote1 + 1 ..];
            const quote2 = std.mem.indexOf(u8, str, '"') orelse break;
            const key = str[0..quote2];
            str = str[quote2 + 1 ..];
            const colon = std.mem.indexOf(u8, str, ':') orelse break;
            str = str[colon + 1 ..];
            const quote3 = std.mem.indexOf(u8, str, '"') orelse break;
            str = str[quote3 + 1 ..];
            const quote4 = std.mem.indexOf(u8, str, '"') orelse break;
            const value = str[0..quote4];
            str = str[quote4 + 1 ..];
            _ = try map.put(key, value);
        }
        return map;
    }
};
// Note: The above code snippets are illustrative and may require additional error handling and refinements for production use.

