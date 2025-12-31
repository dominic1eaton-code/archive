const std = @import("std");
const registry = @import("registry.zig");

pub fn installPackage(allocator: *std.mem.Allocator, packageName: []const u8) !void {
    const base_url = "https://example.com/packages/";

    const meta_url = std.fmt.allocPrint(allocator, "{s}.json", .{packageName}) catch return error.OutOfMemory;
    defer allocator.free(meta_url);

    const meta = try registry.fetchPackageMeta(meta_url, allocator);

    if (meta.dependencies) |deps| {
        var iter = deps.entries();
        while (iter.next()) |entry| {
            try installPackage(allocator, entry.key);
        }
    }

    try downloadAndExtract(allocator, meta.url, meta.name);
}


pub fn installPackage(allocator: *std.mem.Allocator, packageName: []const u8) !void {
    const meta = try registry.fetchPackageMeta(packageName, allocator);

    // Recursively install dependencies
    if (meta.dependencies) |deps| {
        var iter = deps.entries();
        while (iter.next()) |entry| {
            try installPackage(allocator, entry.key);
        }
    }

    // Skip if package already installed
    const pkg_path = std.fmt.allocPrint(allocator, "packages/{s}", .{meta.name}) catch return error.OutOfMemory;
    defer allocator.free(pkg_path);

    const fs = std.fs.cwd();
    if (fs.dirExists(pkg_path)) {
        return; // Already installed
    }

    try fs.createDirectory(pkg_path, .{});

    // Copy zip contents (simulation)
    const zip_file = try fs.openFile(meta.url, .{});
    defer zip_file.close();

    const buffer = try zip_file.readToEndAlloc(allocator, 1024);
    defer allocator.free(buffer);

    const out_file = try fs.createFile(std.fmt.allocPrint(allocator, "{s}/dummy.txt", .{meta.name}) catch return error.OutOfMemory, .{});
    defer out_file.close();
    try out_file.writeAll(buffer);

    std.debug.print("Installed package: {s}\n", .{meta.name});
}

fn downloadAndExtract(allocator: *std.mem.Allocator, url: []const u8, name: []const u8) !void {
    const client = try std.net.http.Client.init(allocator);
    defer client.deinit();

    const response = try client.get(url, std.time.Clock.default());
    defer response.close();

    const body = try response.bodyAsSliceAlloc(allocator);
    defer allocator.free(body);

    const out_dir = std.fs.cwd().createDirectory(name, .{}) catch {};
    const out_file_path = std.fmt.allocPrint(allocator, "{s}/{s}.zip", .{ name, name }) catch return error.OutOfMemory;
    defer allocator.free(out_file_path);

    const out_file = try std.fs.cwd().createFile(out_file_path, .{});
    defer out_file.close();

    try out_file.writeAll(body);
    try std.archive.Zip.extract(allocator, out_file_path, name) catch {};
}

pub fn validateSemVer(version: []const u8) bool {
    var parts: [3]usize = undefined;
    var idx: usize = 0;
    var start: usize = 0;
    for (version) |c, i| {
        if (c == '.') {
            if (idx >= 3) return false;
            const part = version[start..i];
            if (part.len == 0) return false;
            const parsed = std.fmt.parseInt(usize, part, 10) orelse return false;
            parts[idx] = parsed;
            idx += 1;
            start = i + 1;
        }
    }
    if (idx < 2) return false;
    const part = version[start..];
    if (part.len == 0) return false;
    const parsed = std.fmt.parseInt(usize, part, 10) orelse return false;
    parts[idx] = parsed;
    idx += 1;

    return idx == 3;
}
