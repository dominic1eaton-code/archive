const std = @import("std");

pub fn resolveVersion(requested: []const u8, available: [][]const u8) ![]const u8 {
    if (std.mem.eql(u8, requested, "latest")) {
        var latest = available[0];
        for (available) |v| {
            if (compareSemVer(v, latest) > 0) latest = v;
        }
        return latest;
    }

    // Simple range: "^1.2.0" -> pick highest matching major version
    if (requested[0] == '^') {
        const major = try std.fmt.parseInt(u32, requested[1..], 10);
        var matched: []const u8 = "";
        for (available) |v| {
            const v_major = try parseMajor(v);
            if (v_major == major) {
                if (compareSemVer(v, matched) > 0) matched = v;
            }
        }
        if (matched == "") return error.NoMatchingVersion;
        return matched;
    }

    // Exact version
    for (available) |v| if (std.mem.eql(u8, v, requested)) return requested;
    return error.VersionNotFound;
}

fn parseMajor(version: []const u8) !u32 {
    const parts = std.mem.split(u8, version, ".");
    return try std.fmt.parseInt(u32, parts[0], 10);
}

fn compareSemVer(a: []const u8, b: []const u8) i32 {
    const splitA = std.mem.split(u8, a, ".");
    const splitB = std.mem.split(u8, b, ".");
    for (0..3) |i| {
        const ai = std.fmt.parseInt(u32, splitA[i], 10) catch 0;
        const bi = std.fmt.parseInt(u32, splitB[i], 10) catch 0;
        if (ai < bi) return -1;
        if (ai > bi) return 1;
    }
    return 0;
}
pub const error = struct {
    NoMatchingVersion: error{},
    VersionNotFound: error{},
};