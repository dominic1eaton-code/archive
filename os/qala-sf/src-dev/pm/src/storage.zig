const std = @import("std");

pub fn saveArtifact(filePath: []const u8, artifact: Artifact) !void {
    const fs = std.fs.cwd();
    const file = try fs.createFile(filePath, .{ .truncate = true });
    defer file.close();
    try file.writeAll(artifact.hash); // Save artifact data; expand to store the actual file
}

pub fn loadArtifact(filePath: []const u8) !Artifact {
    const fs = std.fs.cwd();
    const file = try fs.openFile(filePath, .{});
    defer file.close();

    var buffer: [1024]u8 = undefined;
    const read_len = try file.read(buffer[0..]);
    return Artifact{
        .name = "example",
        .version = "0.1.0",
        .hash = buffer[0..read_len],
        .created_at = std.time.milliTimestamp(),
        .path = filePath,
    };
}

pub fn saveFile(baseDir: []const u8, name: []const u8, version: []const u8, data: []const u8) ![]const u8 {
    const allocator = std.heap.page_allocator;
    const path = try std.fmt.allocPrint(allocator, "{s}/{s}-{s}", .{ baseDir, name, version });
    defer allocator.free(path);

    var file = try std.fs.cwd().createFile(path, .{ .truncate = true });
    defer file.close();
    try file.writeAll(data);
    return path;
}

pub fn loadFile(path: []const u8) ![]u8 {
    const fs = std.fs.cwd();
    var file = try fs.openFile(path, .{});
    defer file.close();

    const stat = try file.stat();
    const len = stat.size;
    var buf = try std.heap.page_allocator.alloc(u8, len);
    _ = try file.readAll(buf[0..len]);
    return buf;
}
