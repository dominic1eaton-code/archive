const std = @import("std");

pub const PackageMeta = struct {
    name: []const u8,
    version: []const u8,
    dependencies: ?std.json.Object,
    url: []const u8,
};

pub fn fetchPackageMeta(url: []const u8, allocator: *std.mem.Allocator) !PackageMeta {
    const client = try std.net.http.Client.init(allocator);
    defer client.deinit();

    const response = try client.get(url, std.time.Clock.default());
    defer response.close();

    const body = try response.bodyAsSliceAlloc(allocator);
    defer allocator.free(body);

    const json = try std.json.parse(allocator, body);

    const obj = json.Object();
    const name = obj.get("name") orelse return error.InvalidJSON;
    const version = obj.get("version") orelse return error.InvalidJSON;
    const deps = obj.get("dependencies");
    const download_url = obj.get("url") orelse return error.InvalidJSON;

    return PackageMeta{
        .name = name.String() catch return error.InvalidJSON,
        .version = version.String() catch return error.InvalidJSON,
        .dependencies = deps,
        .url = download_url.String() catch return error.InvalidJSON,
    };
}

pub const Version = struct {
    major: u32,
    minor: u32,
    patch: u32,

    pub fn parse(version: []const u8) ?Version {
        var parts: [3]u32 = undefined;
        var idx: usize = 0;
        var start: usize = 0;
        for (version) |c, i| {
            if (c == '.') {
                if (idx >= 3) return null;
                const part = version[start..i];
                const parsed = std.fmt.parseInt(u32, part, 10) orelse return null;
                parts[idx] = parsed;
                idx += 1;
                start = i + 1;
            }
        }
        if (idx < 2) return null;
        const part = version[start..];
        const parsed = std.fmt.parseInt(u32, part, 10) orelse return null;
        parts[idx] = parsed;
        idx += 1;

        if (idx != 3) return null;
        return Version{ .major = parts[0], .minor = parts[1], .patch = parts[2] };
    }

    pub fn parse(version: []const u8) ?Version {
        var parts: [3]u32 = undefined;
        var idx: usize = 0;
        var start: usize = 0;
        for (version) |c, i| {
            if (c == '.') {
                if (idx >= 3) return null;
                const part = version[start..i];
                const parsed = std.fmt.parseInt(u32, part, 10) orelse return null;
                parts[idx] = parsed;
                idx += 1;
                start = i + 1;
            }
        }
        if (idx < 2) return null;
        const part = version[start..];
        const parsed = std.fmt.parseInt(u32, part, 10) orelse return null;
        parts[idx] = parsed;
        idx += 1;

        if (idx != 3) return null;
        return Version{ .major = parts[0], .minor = parts[1], .patch = parts[2] };
    }
    pub fn increment(self: Version, level: []const u8) Version {
        switch (level) {
            "patch" => return Version{ .major = self.major, .minor = self.minor, .patch = self.patch + 1 },
            "minor" => return Version{ .major = self.major, .minor = self.minor + 1, .patch = 0 },
            "major" => return Version{ .major = self.major + 1, .minor = 0, .patch = 0 },
            else => return self,
        }
    }
    pub fn toString(self: Version, allocator: *std.mem.Allocator) ![]u8 {
        return try std.fmt.allocPrint(allocator, "{d}.{d}.{d}", .{self.major, self.minor, self.patch});
    }
};


pub const PackageMeta = struct {
    name: []const u8,
    version: []const u8,
    dependencies: ?std.json.Object,
    url: []const u8,
};

pub fn fetchPackageMeta(name: []const u8, allocator: *std.mem.Allocator) !PackageMeta {
    const path = std.fmt.allocPrint(allocator, "registry/{s}.json", .{name}) catch return error.OutOfMemory;
    defer allocator.free(path);

    const file = try std.fs.cwd().openFile(path, .{});
    defer file.close();

    const content = try file.readToEndAlloc(allocator, 1024);
    defer allocator.free(content);

    const json = try std.json.parse(allocator, content);
    const obj = json.Object();

    const dependencies = obj.get("dependencies");
    const name_val = obj.get("name") orelse return error.InvalidJSON;
    const version_val = obj.get("version") orelse return error.InvalidJSON;
    const url_val = obj.get("url") orelse return error.InvalidJSON;

    return PackageMeta{
        .name = name_val.String() catch return error.InvalidJSON,
        .version = version_val.String() catch return error.InvalidJSON,
        .dependencies = dependencies,
        .url = url_val.String() catch return error.InvalidJSON,
    };
}

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

    for (parts) |part| {
        if (part.len == 0) return false;
        for (part) |c| {
            if (c < '0' or c > '9') return false;
        }
    }
    return true;
}
pub fn incrementVersion(version: []const u8, level: []const u8) ?[]u8 {
    const ver = Version.parse(version) orelse return null;
    const new_ver = ver.increment(level);
    return new_ver.toString(allocator) catch return null;
}