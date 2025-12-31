// Artifact Storage
const std = @import("std");

pub const Artifacts = struct {
    allocator: *std.mem.Allocator,
    base_path: []const u8, // "/var/lib/mini-cd/artifacts"

    pub fn init(a: *std.mem.Allocator, base: []const u8) Artifacts {
        return .{ .allocator = a, .base_path = base };
    }

    pub fn writeJobArtifact(self: *Artifacts, job_id: u32, name: []const u8, data: []const u8) !void {
        var dir_path = try std.fmt.allocPrint(self.allocator, "{s}/jobs/{d}", .{ self.base_path, job_id });
        defer self.allocator.free(dir_path);

        var dir = try std.fs.cwd().makeOpenPath(dir_path, .{});
        defer dir.close();

        var file = try dir.createFile(name, .{});
        defer file.close();
        try file.writeAll(data);
    }

    pub fn readJobArtifact(self: *Artifacts, allocator: *std.mem.Allocator, job_id: u32, name: []const u8) ![]u8 {
        var path = try std.fmt.allocPrint(allocator, "{s}/jobs/{d}/{s}", .{ self.base_path, job_id, name });
        defer allocator.free(path);

        var file = try std.fs.cwd().openFile(path, .{});
        defer file.close();

        return file.readToEndAlloc(allocator, 100 * 1024 * 1024); // 100MB max
    }

    pub fn expireOlderThan(self: *Artifacts, days: u32) !void {
        // walk directory, compare mtime, delete
        // omitted for brevity
    }
};
