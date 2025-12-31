// Plugin registry + metadata
const std = @import("std");
const fs = std.fs;

pub const Plugin = struct {
    name: []const u8,
    versions_url: []const u8, // JSON with available versions
    bin_path_template: []const u8, // {version}/bin/{tool}
    download_url_template: []const u8,  // URL template for downloads
};



// pub fn addPlugin(allocator: *std.mem.Allocator, name: []const u8, versions_url: []const u8, bin_template: []const u8) !void {
//     const dir = try std.fs.cwd().createDir(name, .{});
//     defer dir.close();
//     const file = try dir.createFile("plugin.json", .{});
//     defer file.close();
//     const data = std.fmt.allocPrint(allocator, "{{\"name\":\"{s}\",\"versions_url\":\"{s}\",\"bin_path_template\":\"{s}\"}}", .{ name, versions_url, bin_template });
//     try file.writeAll(data);
// }
pub fn addPlugin(allocator: *std.mem.Allocator, name: []const u8, versions_url: []const u8, bin_template: []const u8, download_template: []const u8) !void {
    const plugins_dir = try std.fmt.allocPrint(allocator, "{s}/plugins", .{ "~/.envmgr" });
    _ = try std.fs.cwd().createDirAll(plugins_dir, 0o755);

    const plugin_path = try std.fmt.allocPrint(allocator, "{s}/{s}.json", .{ plugins_dir, name });
    var file = try std.fs.cwd().createFile(plugin_path, .{});
    defer file.close();

    const json = std.fmt.allocPrint(allocator,
        "{{\"name\":\"{s}\",\"versions_url\":\"{s}\",\"bin_path_template\":\"{s}\",\"download_url_template\":\"{s}\"}}",
        .{ name, versions_url, bin_template, download_template });
    try file.writeAll(json);
}

pub fn getPlugin(allocator: *std.mem.Allocator, name: []const u8) !Plugin {
    const dir = try std.fs.cwd().openDir(name);
    defer dir.close();
    const file = try dir.openFile("plugin.json", .{});
    defer file.close();
    const data = try file.readToEndAlloc(allocator, 1024);
    defer allocator.free(data);

    var parser = std.json.Parser.init(data);
    const root = try parser.parseRoot();
    const obj = root.Object();

    return Plugin{
        .name = obj.getString("name") orelse "",
        .versions_url = obj.getString("versions_url") orelse "",
        .bin_path_template = obj.getString("bin_path_template") orelse "",
        .download_url_template = obj.getString("download_url_template") orelse "",
    };
}
pub fn removePlugin(allocator: *std.mem.Allocator, name: []const u8) !void {
    const path = try std.fmt.allocPrint(allocator, "{s}/plugins/{s}.json", .{ "~/.envmgr", name });
    try std.fs.cwd().deleteFile(path);
}
pub fn listPlugins(allocator: *std.mem.Allocator) ![]Plugin {
    var plugins = std.ArrayList(Plugin).init(allocator);
    defer plugins.deinit();
    const plugins_dir = try std.fmt.allocPrint(allocator, "{s}/plugins", .{ "~/.envmgr" });
    var dir = try std.fs.cwd().openDir(plugins_dir);
    defer dir.close();
    var it = dir.iterate();
    while (try it.next()) |entry| {
        if (entry.kind == .File and std.mem.endsWith(u8, entry.name, ".json")) {
            const plugin_name = entry.name[0..entry.name.len - 5]; // remove .json
            const plugin = try getPlugin(allocator, plugin_name);
            try plugins.append(plugin);
        }
    }
    return plugins.toOwnedSlice();
}

pub fn loadPlugin(allocator: *std.mem.Allocator, name: []const u8) !Plugin {
    const path = try std.fmt.allocPrint(allocator, "{s}/plugins/{s}.json", .{ "~/.envmgr", name });
    var file = try std.fs.cwd().openFile(path, .{ .read = true });
    defer file.close();

    var buffer: [4096]u8 = undefined;
    const bytes = try file.readAll(&buffer);
    const json_str = buffer[0..bytes];

    const parser = std.json.Parser.init(allocator, json_str);
    const root = try parser.parseRoot();
    const obj = root.Object() catch return error.InvalidJSON;

    return Plugin{
        .name = obj.getString("name") orelse return error.MissingField,
        .versions_url = obj.getString("versions_url") orelse return error.MissingField,
        .bin_path_template = obj.getString("bin_path_template") orelse return error.MissingField,
        .download_url_template = obj.getString("download_url_template") orelse return error.MissingField,
    };
}

pub const error = struct {
    PluginNotFound: error{},
    InvalidJSON: error{},
    MissingField: error{},
};

pub fn listPluginVersions(plugin: Plugin, allocator: *std.mem.Allocator) ![][]const u8 {
    // Fetch JSON from plugin.versions_url
    const allocator_ptr = allocator;
    var cmd = &[_][]const u8{"curl", "-s", plugin.versions_url};
    var process = try std.ChildProcess.init(allocator_ptr).spawn(.{ .argv = cmd }) catch unreachable;
    defer process.deinit();
    const status = try process.wait();

    if (status != 0) return error.DownloadFailed;

    // For simplicity, assume JSON array with version strings
    // In real implementation, parse JSON array
    return [][]const u8{}; // stub
}

const json = std.json;

pub fn fetchPluginVersions(allocator: *std.mem.Allocator, plugin: Plugin) ![][]const u8 {
    // Download JSON from versions_url
    const curl_cmd = &[_][]const u8{"curl", "-s", plugin.versions_url};
    var process = try std.ChildProcess.init(allocator).spawn(.{ .argv = curl_cmd }) catch unreachable;
    defer process.deinit();
    const status = try process.wait();
    if (status != 0) return error.DownloadFailed;

    var stdout_buf: [4096]u8 = undefined;
    const n = try process.stdout().readAll(&stdout_buf);
    const json_str = stdout_buf[0..n];

    // Parse JSON array of version strings
    var parser = json.Parser.init(allocator, json_str);
    const root = try parser.parseRoot();
    var versions: [][]const u8 = &[_][]const u8{}; // dynamic array stub

    const array = root.Array() catch return error.InvalidJSON;
    for (array.items) |item| {
        const v = item.String() catch continue;
        versions = versions ++ &[_][]const u8{v};
    }
    return versions;
}
pub const error = struct {
    DownloadFailed: error{},
    InvalidJSON: error{},
};
