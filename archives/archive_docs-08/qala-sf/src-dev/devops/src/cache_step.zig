// @license("MIT")
// @brief("")
// @author("qala development team")
// @copyright("2024 qala development team")
const std = @import("std");

pub fn computeStepHash(
    allocator: std.mem.Allocator,
    job_name: []const u8,
    step_index: usize,
    command: []const u8,
    dep_hashes: []const []const u8,
) ![]u8 {
    var h = std.crypto.hash.sha256.Sha256.init(.{});
    h.update(job_name);
    h.update(std.mem.asBytes(&step_index));
    h.update(command);

    for (dep_hashes) |dh| h.update(dh);

    const digest = h.finalResult();

    var out = try allocator.alloc(u8, digest.len);
    std.mem.copy(u8, out, digest[0..]);
    return out;
}

pub fn stepCacheDir(
    allocator: std.mem.Allocator,
    job: []const u8,
    index: usize,
) ![]const u8 {
    return try std.fs.path.join(allocator, &[_][]const u8{
        ".ci_cache", "steps", job,
    });
}

pub fn checkStepCache(
    allocator: std.mem.Allocator,
    job_name: []const u8,
    step_index: usize,
    hash: []const u8,
) !bool {
    const dir = try stepCacheDir(allocator, job_name, step_index);

    var cwd = std.fs.cwd();
    var d = cwd.openDir(dir, .{}) catch return false;
    defer d.close();

    const name = try std.fmt.allocPrint(allocator, "{d}.hash", .{step_index});
    const stored = d.readFileAlloc(allocator, name, 1024) catch return false;

    return std.mem.eql(u8, stored, hash);
}

pub fn storeStepCache(
    allocator: std.mem.Allocator,
    job_name: []const u8,
    step_index: usize,
    hash: []const u8,
) !void {
    const dir = try stepCacheDir(allocator, job_name, step_index);

    var cwd = std.fs.cwd();
    try cwd.makePath(dir);

    var d = try cwd.openDir(dir, .{});
    defer d.close();

    const name = try std.fmt.allocPrint(allocator, "{d}.hash", .{step_index});
    try d.writeFile(name, hash);
}
