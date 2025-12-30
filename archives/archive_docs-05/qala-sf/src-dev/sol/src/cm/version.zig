// SPDX-License-Identifier: MIT
//  Copyright (c) 2024 Qala Systems Inc.
//  All rights reserved.
//  This source code is licensed under the MIT license found in the
//  LICENSE file in the root directory of this source tree.
//  https://opensource.org/license/mit/
//  Author: Qala Systems Inc.
//  Date:
//  Description: Semantic Versioning utilities
//  Module: cm.version
// --------------------------------------------

const std = @import("std"); 


pub const Version = struct {
    major: u32,
    minor: u32,
    patch: u32,

    pub fn parse(version: []const u8) ?Version {
        var parts: [3]u32 = undefined;
        var idx: usize = 0;
        var start: usize = 0;
        for (version) |c, i| {
            if (c == '.' or i == version.len - 1) {
                const end = if (i == version.len - 1) i + 1 else i;
                const num = try std.fmt.parseInt(u32, version[start..end], 10);
                if (idx >= 3) return null;
                parts[idx] = num;
                idx += 1;
                start = i + 1;
            }
        }
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

pub fn compare(a: Version, b: Version) i32 {
    if (a.major != b.major) return if (a.major < b.major) -1 else 1;
    if (a.minor != b.minor) return if (a.minor < b.minor) -1 else 1;
    if (a.patch != b.patch) return if (a.patch < b.patch) -1 else 1;
    return 0;
}
pub fn validateSemVer(version: []const u8) bool {
    return Version.parse(version) != null;
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
    var allocator = std.heap.page_allocator;
    return try new_ver.toString(&allocator);
}

pub fn gitTag(version: []const u8) !void {
    const result = try std.process.exec(&[_][]const u8{"git", "add", "."}, .{});
    _ = result.wait();
    const commit = try std.process.exec(&[_][]const u8{"git", "commit", "-m", "Release " ++ version}, .{});
    _ = commit.wait();
    const tag = try std.process.exec(&[_][]const u8{"git", "tag", version}, .{});
    _ = tag.wait();
    const push = try std.process.exec(&[_][]const u8{"git", "push", "--follow-tags"}, .{});
    _ = push.wait();
}

pub fn dockerDeploy(version: []const u8, env: []const u8) !void {
    const build = try std.process.exec(&[_][]const u8{"docker", "build", "-t", "myapp:" ++ version, "."}, .{});
    _ = build.wait();
    const run = try std.process.exec(&[_][]const u8{"docker", "run", "-d", "--name", env, "myapp:" ++ version}, .{});
    _ = run.wait();
}

pub fn interactiveMenu() ![]const u8 {
    const stdin = std.io.getStdIn().reader();
    const stdout = std.io.getStdOut().writer();

    try stdout.print("Select release type:\n1. Patch\n2. Minor\n3. Major\n> ", .{});
    var input = try stdin.readLineAlloc(std.heap.page_allocator, 10);
    defer std.heap.page_allocator.free(input);

    return switch (input) {
        "1" => "patch",
        "2" => "minor",
        "3" => "major",
        else => "patch",
    };
}

pub fn printVersionInfo(version: []const u8) void {
    std.debug.print("Current Version: {s}\n", .{version});
}

pub fn printUsage() void {
    std.debug.print("Usage: version_manager [increment|tag|deploy|info|menu]\n", .{});
}

pub fn workflow() void {
    const allocator = std.heap.page_allocator;
    var releases = try storage.loadReleases("releases.json", allocator);

    const latestVersionStr = if (releases.len > 0) releases[releases.len - 1].version else "0.0.0";
    var latestVersion = try Version.parse(latestVersionStr) orelse Version{0,0,0};

    const releaseType = try interactiveMenu();
    var newVersion = latestVersion.increment(releaseType);
    const newVersionStr = try newVersion.toString(allocator);

    const notes = "Automatic release generated"; // Could also be interactive input
    const env = Release.Environment.Staging;

    const release = try Release.newRelease(newVersionStr, notes, null, env, allocator);
    releases = try allocator.realloc(Release, releases, releases.len + 1);
    releases[releases.len - 1] = release;

    try storage.saveReleases("releases.json", releases, allocator);

    // Git + Docker deployment
    try gitTag(newVersionStr);
    try dockerDeploy(newVersionStr, if (env == .Staging) "staging" else "production");

    std.debug.print("Release {s} deployed!\n", .{newVersionStr});
}
