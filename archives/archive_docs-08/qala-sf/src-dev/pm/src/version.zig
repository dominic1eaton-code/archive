const std = @import("std");
const sqlite = @import("sqlite.zig");

pub fn getLatestVersion(artifacts: []Artifact) Artifact {
    var latest: Artifact = artifacts[0];
    for (artifacts) |artifact| {
        if (compareVersion(artifact.version, latest.version) > 0) {
            latest = artifact;
        }
    }
    return latest;
}

fn compareVersion(v1: []const u8, v2: []const u8) i32 {
    var a = parseVersion(v1);
    var b = parseVersion(v2);
    if (a.major != b.major) return a.major - b.major;
    if (a.minor != b.minor) return a.minor - b.minor;
    return a.patch - b.patch;
}

fn parseVersion(v: []const u8) struct { major: i32, minor: i32, patch: i32 } {
    // parse "x.y.z" into numbers (simple implementation)
    var parts = std.mem.split(v, ".") orelse return .{ 0, 0, 0 };
    return .{ .major = std.fmt.parseInt(i32, parts[0], 10) orelse 0, .minor = std.fmt.parseInt(i32, parts[1], 10) orelse 0, .patch = std.fmt.parseInt(i32, parts[2], 10) orelse 0 };
}

pub const SemVer = struct {
    major: u32,
    minor: u32,
    patch: u32,
};

pub fn parse(version: []const u8) ?SemVer {
    var parts = std.mem.split(version, ".");
    var it = parts.iterator();
    const maj = try it.next() orelse return null;
    const min = try it.next() orelse return null;
    const pat = try it.next() orelse return null;
    const major = std.fmt.parseInt(u32, maj, 10) catch return null;
    const minor = std.fmt.parseInt(u32, min, 10) catch return null;
    const patch = std.fmt.parseInt(u32, pat, 10) catch return null;
    return SemVer{ .major = major, .minor = minor, .patch = patch };
}

pub fn cmp(a: SemVer, b: SemVer) i32 {
    if (a.major != b.major) return if (a.major < b.major) -1 else 1;
    if (a.minor != b.minor) return if (a.minor < b.minor) -1 else 1;
    if (a.patch != b.patch) return if (a.patch < b.patch) -1 else 1;
    return 0;
}

pub fn isNewer(a: []const u8, b: []const u8) bool {
    const va = parse(a) orelse return false;
    const vb = parse(b) orelse return false;
    return cmp(va, vb) > 0;
}
