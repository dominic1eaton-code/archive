const std = @import("std");
const Controller = @import("controller.zig").Controller;

pub fn main() !void {
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    defer _ = gpa.deinit();
    const allocator = &gpa.allocator;

    var args = std.process.args();
    _ = args.skip(); // binary name

    const cmd = args.next() orelse {
        std.debug.print("Usage: mini-cd-controller {start|validate-config|list-pipelines|run-pipeline}\n", .{});
        return;
    };

    if (std.mem.eql(u8, cmd, "start")) {
        var controller = try Controller.init(allocator, "/etc/mini-cd/config.json");
        try controller.start();
    } else if (std.mem.eql(u8, cmd, "validate-config")) {
        try Controller.validateConfig("/etc/mini-cd/config.json");
        std.debug.print("OK\n", .{});
    } else if (std.mem.eql(u8, cmd, "list-pipelines")) {
        var controller = try Controller.init(allocator, "/etc/mini-cd/config.json");
        controller.listPipelines();
    } else if (std.mem.eql(u8, cmd, "run-pipeline")) {
        const pipeline_name = args.next() orelse return error.MissingPipelineName;
        var controller = try Controller.init(allocator, "/etc/mini-cd/config.json");
        try controller.runPipelineByName(pipeline_name);
    } else {
        std.debug.print("Unknown command\n", .{});
        return;
    }
}
