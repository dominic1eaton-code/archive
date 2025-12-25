const std = @import("std");
const Agent = @import("agent.zig").Agent;

pub fn main() !void {
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    defer _ = gpa.deinit();
    const allocator = &gpa.allocator;

    var args = std.process.args();
    _ = args.skip();

    const cmd = args.next() orelse {
        std.debug.print("Usage: mini-cd-agent {start|test}\n", .{});
        return;
    };

    if (std.mem.eql(u8, cmd, "start")) {
        var agent = try Agent.init(allocator, "/etc/mini-cd/agent.json");
        try agent.start();
    } else if (std.mem.eql(u8, cmd, "test")) {
        std.debug.print("Agent OK\n", .{});
    } else {
        std.debug.print("Unknown command\n", .{});
    }
}
