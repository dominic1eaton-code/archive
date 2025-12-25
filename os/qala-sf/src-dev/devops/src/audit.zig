const std = @import("std");
const json = std.json;

pub const Audit = struct {
    allocator: *std.mem.Allocator,
    log_path: []const u8, // e.g. "/var/log/mini-cd/audit.log"

    pub fn init(allocator: *std.mem.Allocator, path: []const u8) Audit {
        return .{ .allocator = allocator, .log_path = path };
    }

    pub fn logAction(self: *Audit, actor: []const u8, role: []const u8, source: []const u8, action: []const u8, job_id: ?u32, pipeline: ?[]const u8, details: ?json.Value) !void {
        var stdout_writer = std.io.getStdOut().writer(); // For testing
        const ts = std.time.gmtime(std.time.milliTimestamp());

        var log_obj = json.Value.Object.init(self.allocator);
        try log_obj.put("timestamp", ts) catch {};
        try log_obj.put("actor", actor) catch {};
        try log_obj.put("role", role) catch {};
        try log_obj.put("source", source) catch {};
        try log_obj.put("action", action) catch {};
        if (pipeline) try log_obj.put("pipeline", pipeline.?) catch {};
        if (job_id) try log_obj.put("job_id", job_id.?) catch {};
        if (details) try log_obj.put("details", details.?) catch {};

        const log_line = try json.printToString(self.allocator, &log_obj, .{});
        defer self.allocator.free(log_line);

        // Append to log file
        var file = try std.fs.cwd().openFile(self.log_path, .{ .append = true, .create = true });
        defer file.close();
        try file.writeAll(log_line);
        try file.writeAll("\n");
    }
};
