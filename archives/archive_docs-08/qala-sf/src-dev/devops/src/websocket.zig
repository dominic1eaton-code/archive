const std = @import("std");
const Pipeline = @import("pipeline.zig").Pipeline;

pub const WebsocketHub = struct {
    allocator: *std.mem.Allocator,
    conns: std.ArrayList(*std.net.Stream),

    pub fn init(a: *std.mem.Allocator) WebsocketHub {
        return .{
            .allocator = a,
            .conns = std.ArrayList(*std.net.Stream).init(a),
        };
    }

    pub fn broadcast(self: *WebsocketHub, msg: []const u8) void {
        for (self.conns.items) |conn| {
            conn.writer().print("{s}\n", .{msg}) catch {};
        }
    }

    pub fn handleMessage(self: *WebsocketHub, pipeline: *Pipeline, msg: []const u8) void {
        // Commands: {"trigger": 2}
        if (std.mem.containsAtLeast(u8, msg, 1, "trigger")) {
            const id = std.fmt.parseInt(u32, msg["trigger"], 10) catch return;
            pipeline.trigger(id) catch return;
        }
    }
};
