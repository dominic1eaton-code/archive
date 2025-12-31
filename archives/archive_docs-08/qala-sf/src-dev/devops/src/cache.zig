// @license("MIT")
// @brief("")
// @author("qala development team")
// @copyright("2024 qala development team")
const std = @import("std");
const Job = @import("config.zig").Job;

pub const CacheResult = enum {
    Hit,
    Miss,
};

pub fn computeJobHash(
    allocator: std.mem.Allocator,
    job: Job,
    dependencies: []const []const u8, // paths or hashes from dependent jobs
) ![]u8 {
    var hasher = std.crypto.hash.sha256.Sha256.init(.{});

    // hash job name
    hasher.update(job.name);

    // hash commands
    for (job.steps) |st| {
        hasher.update(st.command);
    }

    // hash dependency outputs
    for (dependencies) |dep| {
        hasher.update(dep);
    }

    const digest = hasher.finalResult();
    var out = try allocator.alloc(u8, digest.len);
    std.mem.copy(u8, out, digest[0..]);
    return out;
}

pub fn cacheDir(allocator: std.mem.Allocator, job_name: []const u8) ![]const u8 {
    return try std.fs.path.join(allocator, &[_][]const u8{
        ".ci_cache", "jobs", job_name,
    });
}

pub fn checkCache(
    allocator: std.mem.Allocator,
    job: Job,
    hash: []const u8,
) !CacheResult {
    const dir = try cacheDir(allocator, job.name);

    var cwd = std.fs.cwd();
    var cache = cwd.openDir(dir, .{}) catch return CacheResult.Miss;

    defer cache.close();

    // read hash file
    const hash_path = "hash";
    const stored = cache.readFileAlloc(allocator, hash_path, 1024) catch return CacheResult.Miss;

    if (std.mem.eql(u8, stored, hash))
        return CacheResult.Hit;

    return CacheResult.Miss;
}

pub fn storeCache(
    allocator: std.mem.Allocator,
    job: Job,
    hash: []const u8,
    artifact_path: []const u8,
) !void {
    var cwd = std.fs.cwd();

    const dir = try cacheDir(allocator, job.name);
    try cwd.makePath(dir);

    var cache = try cwd.openDir(dir, .{});
    defer cache.close();

    // write hash
    try cache.writeFile("hash", hash);

    // copy artifact into cache as "artifact.tar"
    try cwd.copyFile(artifact_path, cache, "artifact.tar", .{});
}

pub fn tryLoadFromCache(
    allocator: std.mem.Allocator,
    action_hash: []const u8,
) !?[]u8 {
    const path = try std.fmt.allocPrint(allocator, "cache/{s}/attestation.json", .{action_hash});

    var file = std.fs.cwd().openFile(path, .{}) catch return null;
    defer file.close();

    const att = try file.readToEndAlloc(allocator, 64 * 1024);

    if (try replayMatch(allocator, att, action_hash) == .Match) {
        // Load bundled artifact
        const cab = try std.fs.cwd().readFileAlloc(allocator, try std.fmt.allocPrint(allocator, "cache/{s}/artifact.cab", .{action_hash}), 512 * 1024 * 1024);
        return cab;
    }

    return null;
}

pub fn computeCacheKey(job: *Job, deps: [][]const u8) ![32]u8 {
    var hasher = std.crypto.hash.sha2.Sha256.init(.{});
    hasher.update(job.name);
    hasher.update(job.command);

    for (deps) |dep| hasher.update(dep);

    return hasher.finalResult();
}

pub const Cache = struct {
    allocator: *std.mem.Allocator,
    base_path: []const u8, // "/var/cache/mini-cd"

    pub fn init(a: *std.mem.Allocator, path: []const u8) Cache {
        return .{ .allocator = a, .base_path = path };
    }

    fn keyHex(key: [32]u8, buf: *[64]u8) []const u8 {
        return std.fmt.bufPrint(buf, "{x}", .{key}) catch unreachable;
    }

    pub fn exists(self: *Cache, key: [32]u8) bool {
        var name_buf: [64]u8 = undefined;
        const name = keyHex(key, &name_buf);
        return std.fs.cwd().access(std.fs.pathJoin(self.allocator, &.{ self.base_path, "cas", name }), .{}) == .success;
    }

    pub fn load(self: *Cache, key: [32]u8, allocator: *std.mem.Allocator) ![]u8 {
        var name_buf: [64]u8 = undefined;
        const name = keyHex(key, &name_buf);

        var file_path = try std.fs.path.join(allocator, &.{ self.base_path, "cas", name });
        defer allocator.free(file_path);

        var file = try std.fs.cwd().openFile(file_path, .{ .read = true });
        defer file.close();
        return file.readToEndAlloc(allocator, 10 * 1024 * 1024); // 10MB max
    }

    pub fn store(self: *Cache, key: [32]u8, data: []const u8) !void {
        var name_buf: [64]u8 = undefined;
        const name = keyHex(key, &name_buf);

        var dir = try std.fs.cwd().makeOpenPath(std.fmt.allocPrint(self.allocator, "{s}/cas", .{self.base_path}), .{});
        defer dir.close();

        var file = try dir.createFile(name, .{});
        defer file.close();
        try file.writeAll(data);
    }
};
