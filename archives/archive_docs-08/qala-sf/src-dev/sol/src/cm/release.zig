const std = @import("std");

pub const Release = struct {
    version: []const u8,
    date: []const u8,
    notes: []const u8,
};

pub fn newRelease(version: []const u8, notes: []const u8, allocator: *std.mem.Allocator) !Release {
    const date = try std.time.format("%Y-%m-%d", try std.time.now());
    return Release{
        .version = version,
        .date = date,
        .notes = notes,
    };
}

pub fn printRelease(release: Release) void {
    std.debug.print("Release Version: {s}\n", .{release.version});
    std.debug.print("Release Date: {s}\n", .{release.date});
    std.debug.print("Release Notes: {s}\n", .{release.notes});
}


pub const Environment = enum { Staging, Production };

pub const Release = struct {
    version: []const u8,
    date: []const u8,
    notes: []const u8,
    tag: ?[]const u8,
    env: Environment,

    pub fn toJson(self: Release, allocator: *std.mem.Allocator) ![]u8 {
        const json_obj = std.json.Object.init(allocator);
        try json_obj.put("version", self.version);
        try json_obj.put("date", self.date);
        try json_obj.put("notes", self.notes);
        if (self.tag) |t| {
            try json_obj.put("tag", t);
        }
        try json_obj.put("env", if (self.env == .Staging) "staging" else "production");
        return try std.json.stringify(json_obj, allocator);
    }

    pub fn fromJson(json: std.json.Value) Release {
        const obj = json.Object;
        const env_str = obj.getString("env") orelse "staging";
        const env = if (std.mem.eql(u8, env_str, "production")) Environment.Production else Environment.Staging;

        return Release{
            .version = obj.getString("version") orelse "0.0.0",
            .date = obj.getString("date") orelse "unknown",
            .notes = obj.getString("notes") orelse "",
            .tag = obj.getString("tag"),
            .env = env,
        };
    }
};

pub fn newRelease(version: []const u8, notes: []const u8, tag: ?[]const u8, env: Environment, allocator: *std.mem.Allocator) !Release {
    const date = try std.time.format("%Y-%m-%d", try std.time.now());
    if (!validateSemVer(version)) return error.InvalidVersion;
    return Release{
        .version = version,
        .date = date,
        .notes = notes,
        .tag = tag,
        .env = env,
    };
}

// Basic Semantic Version validation (major.minor.patch)
pub fn validateSemVer(version: []const u8) bool {
    var parts: [3][]const u8 = undefined;
    var count: usize = 0;
    var start: usize = 0;
    for (version) |c, i| {
        if (c == '.') {
            if (count >= 3) return false;
            parts[count] = version[start..i];
            count += 1;
            start = i + 1;
        }
    }
    if (count != 2) return false;
    parts[2] = version[start..];
    for (parts) |p| {
        for (p) |c| {
            if (c < '0' or c > '9') return false;
        }
    }
    return true;
}

pub const error = struct {
    InvalidVersion: error{},
};

