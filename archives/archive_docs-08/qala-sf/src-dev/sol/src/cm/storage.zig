const std = @import("std");

const Release = @import("release.zig").Release;

pub fn loadReleases(path: []const u8, allocator: *std.mem.Allocator) ![]Release {
    var file = try std.fs.cwd().openFile(path, .{});
    defer file.close();

    const data = try file.readToEndAlloc(allocator, 1024);
    defer allocator.free(data);

    if (data.len == 0) return &[_]Release{}; // empty file

    const parser = std.json.Parser.init(data);
    const value = try parser.parse();
    const arr = value.Array orelse &[_]std.json.Value{};
    var releases: []Release = try allocator.alloc(Release, arr.len);
    for (arr) |v, i| {
        releases[i] = Release.fromJson(v);
    }
    return releases;
}

pub fn saveReleases(path: []const u8, releases: []Release, allocator: *std.mem.Allocator) !void {
    var file = try std.fs.cwd().createFile(path, .{ .truncate = true });
    defer file.close();

    var json_arr = std.json.Array.init(allocator);
    for (releases) |r| {
        const json_str = try r.toJson(allocator);
        defer allocator.free(json_str);
        try json_arr.append(std.json.Value.fromString(json_str));
    }
    const json_data = try std.json.stringify(json_arr, allocator);
    defer allocator.free(json_data);

    try file.writeAll(json_data);
}

pub fn saveRelease(release: Release, path: []const u8) !void {
    const file = try std.fs.cwd().createFile(path, .{});
    defer file.close();
    try file.writeAll(release.version ++ " | " ++ release.date ++ " | " ++ release.notes ++ "\n");
}

pub fn listReleases(path: []const u8) !void {
    const file = try std.fs.cwd().openFile(path, .{});
    defer file.close();
    var reader = file.reader();
    while (true) {
        const line = try reader.readUntilDelimiterOrEofAlloc(&std.heap.page_allocator, '\n');
        if (line.len == 0) break;
        try std.io.getStdOut().writer().print("{s}\n", .{line});
        std.heap.page_allocator.free(line);
    }
}

