// @license("MIT")
// @brief("")
// @author("qala development team")
// @copyright("2024 qala development team")
const std = @import("std");
const devops = @import("devops");
// const Config = @import("config.zig").Config;
// const runPipeline = @import("pipeline.zig").runPipeline;
// pub fn main() !void {
//     var gpa = std.heap.GeneralPurposeAllocator(.{}){};
//     const allocator = gpa.allocator();
//     const args = try std.process.argsAlloc(allocator);
//     defer std.process.argsFree(allocator, args);
//     if (args.len < 2) {
//         std.debug.print("Usage: cibuild <config-file>\n", .{});
//         return;
//     }
//     const path = args[1];
//     const file = try std.fs.cwd().readFileAlloc(allocator, path, 64 * 1024);
//     const config = try Config.parse(allocator, file);
//     try runPipeline(config, allocator);
// }

pub fn main() !void {
    // Prints to stderr, ignoring potential errors.
    std.debug.print("All your {s} are belong to us.\n", .{"codebase"});
    try devops.bufferedPrint();
}

test "simple test" {
    const gpa = std.testing.allocator;
    var list: std.ArrayList(i32) = .empty;
    defer list.deinit(gpa); // Try commenting this out and see if zig detects the memory leak!
    try list.append(gpa, 42);
    try std.testing.expectEqual(@as(i32, 42), list.pop());
}

test "fuzz example" {
    const Context = struct {
        fn testOne(context: @This(), input: []const u8) anyerror!void {
            _ = context;
            // Try passing `--fuzz` to `zig build test` and see if it manages to fail this test case!
            try std.testing.expect(!std.mem.eql(u8, "canyoufindme", input));
        }
    };
    try std.testing.fuzz(Context{}, Context.testOne, .{});
}
