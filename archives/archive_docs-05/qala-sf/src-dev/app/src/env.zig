// Environment management
const std = @import("std");
const util = @import("util.zig");
const fs = std.fs;

pub const EnvManager = struct {
    allocator: *std.mem.Allocator,
    entries: std.StringHashMap([]const u8),

    pub fn init(allocator: *std.mem.Allocator) EnvManager {
        return EnvManager{
            .allocator = allocator,
            .entries = std.StringHashMap([]const u8).init(allocator),
        };
    }

    pub fn deinit(self: *EnvManager) void {
        self.entries.deinit();
    }

    pub fn install(self: *EnvManager, tool: []const u8, version: []const u8, url: []const u8) !void {
        const cache_dir = try util.cacheDir(self.allocator);
        const target_dir = try std.fmt.allocPrint(self.allocator, "{s}/{s}/{s}", .{cache_dir, tool, version});
        defer self.allocator.free(target_dir);

        // Create directory
        _ = try std.fs.cwd().createDirAll(target_dir, 0o755);

        // Download + extract
        try downloadAndExtract(url, target_dir);

        // Set as active
        try self.entries.put(tool, version);
    }

    pub fn setActive(self: *EnvManager, tool: []const u8, version: []const u8) !void {
        try self.entries.put(tool, version);
    }
};

fn downloadAndExtract(url: []const u8, target_dir: []const u8) !void {
    const allocator = std.heap.page_allocator;
    const tmp_file_name = "tmp_download";

    // Download
    const cmd_download = if (std.os.windows()) 
        &[_][]const u8{"powershell", "-Command", "Invoke-WebRequest", url, "-OutFile", tmp_file_name}
    else 
        &[_][]const u8{"curl", "-L", url, "-o", tmp_file_name};

    _ = try std.ChildProcess.init(allocator).spawn(.{ .argv = cmd_download })?.wait();

    // Extract
    const extract_cmd = if (std.mem.endsWith(u8, url, ".zip")) {
        if (std.os.windows()) &[_][]const u8{"powershell", "-Command", "Expand-Archive", tmp_file_name, "-DestinationPath", target_dir}
        else &[_][]const u8{"unzip", tmp_file_name, "-d", target_dir}
    } else {
        &[_][]const u8{"tar", "-xzf", tmp_file_name, "-C", target_dir}
    };

    _ = try std.ChildProcess.init(allocator).spawn(.{ .argv = extract_cmd })?.wait();

    try std.fs.cwd().removeFile(tmp_file_name);
}
pub const error = struct {
    UnsupportedArchive: error{},
};

pub fn install(env: *EnvManager, args: [][]u8) !void {
    if (args.len < 5) return error.InvalidArgument;
    const tool = args[2];
    const version = args[3];
    const url = args[4];

    try env.install(tool, version, url);
    const bin_path = try std.fmt.allocPrint(env.allocator, "{s}/{s}/{s}/bin/{s}", .{ ".envmgr/cache", tool, version, tool });
    try shim.createShim(env.allocator, tool, bin_path);

    // Update lockfile
    const lockfile_path = ".envmgr.lock";
    var lock = try Config.loadLockfile(env.allocator, lockfile_path) orelse std.StringHashMap([]const u8).init(env.allocator);
    _ = try lock.put(tool, version);
    try Config.saveLockfile(env.allocator, lockfile_path, lock);
}

const Config = struct {
    pub fn findConfigFile(allocator: *std.mem.Allocator) !?std.StringHashMap([]const u8) {
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
        var file = try std.fs.cwd().openFile(path, .{ .read = true });
        defer file.close();
        var map = std.StringHashMap([]const u8).init(allocator);
        var reader = file.reader();
        var buf: [1024]u8 = undefined;
        while (true) {
            const line = try reader.readLine(&buf);
            if (line.len == 0) break;
            const trimmed = std.mem.trim(u8, line, " \t\r\n{},\"");
            const idx = std.mem.indexOf(u8, trimmed, ':');
            if (idx) |i| {
                const key = std.mem.trim(u8, trimmed[0..i], " \t\r\n\"");
                const value = std.mem.trim(u8, trimmed[i + 1 ..], " \t\r\n\",");
                _ = try map.put(key, value);
            }
        }
        return map;
    }
};
const shim = @import("shim.zig");
pub const error = struct {
    InvalidArgument: error{},
};
