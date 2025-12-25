const std = @import("std");
const app = @import("app");// Example CLI app
const std = @import("std");
const EnvManager = @import("env.zig").EnvManager;
const commands = @import("commands.zig");

pub fn main() !void {
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    defer std.debug.assert(!gpa.deinit());
    const allocator = gpa.allocator();

    var args = try std.process.argsAlloc(allocator);
    defer std.process.argsFree(allocator, args);

    if (args.len < 2) {
        std.debug.print("Usage: envmgr <command> [args]\n", .{});
        return;
    }

    var env = EnvManager.init(allocator);
    defer env.deinit();

    const cmd = args[1];
    if (std.mem.eql(u8, cmd, "install")) try commands.install(&env, args);
    else if (std.mem.eql(u8, cmd, "plugin")) {
        if (args.len < 3) return error.InvalidArgument;
        const sub = args[2];
        if (std.mem.eql(u8, sub, "add")) {
            try plugin.addPlugin(env.allocator, args[3], args[4], args[5], args[6]);
            std.debug.print("Plugin {s} added\n", .{args[3]});
        }
    }
    else if (std.mem.eql(u8, cmd, "install")) {
        if (args.len < 4) return error.InvalidArgument;
        const plugin_name = args[2];
        const version = args[3];
        try installTool(&env, allocator, plugin_name, version);
    }
    else if (std.mem.eql(u8, cmd, "use")) try commands.use(&env, args);
    else if (std.mem.eql(u8, cmd, "list")) try commands.list(&env);
    else std.debug.print("Unknown command: {s}\n", .{cmd});
}
pub const error = struct {
    InvalidArgument: error{},
};

// pub fn main() !void {
//     // Prints to stderr, ignoring potential errors.
//     std.debug.print("All your {s} are belong to us.\n", .{"codebase"});
//     try app.bufferedPrint();
// }

// test "simple test" {
//     const gpa = std.testing.allocator;
//     var list: std.ArrayList(i32) = .empty;
//     defer list.deinit(gpa); // Try commenting this out and see if zig detects the memory leak!
//     try list.append(gpa, 42);
//     try std.testing.expectEqual(@as(i32, 42), list.pop());
// }

// test "fuzz example" {
//     const Context = struct {
//         fn testOne(context: @This(), input: []const u8) anyerror!void {
//             _ = context;
//             // Try passing `--fuzz` to `zig build test` and see if it manages to fail this test case!
//             try std.testing.expect(!std.mem.eql(u8, "canyoufindme", input));
//         }
//     };
//     try std.testing.fuzz(Context{}, Context.testOne, .{});
// }

// const std = @import("std");
// const router = @import("router.zig").route;
// const Store = @import("store.zig").Store;
// const Handlers = @import("handlers.zig").Handlers;

// pub fn main() !void {
//     var gpa = std.heap.GeneralPurposeAllocator(.{}){};
//     defer _ = gpa.deinit();

//     var store = Store.init(&gpa.allocator);
//     var handlers = Handlers{ .store = &store };

//     var server = try std.http.Server.init(.{});
//     defer server.deinit();

//     try server.listen(.{ .port = 8080 });
//     std.debug.print("Server running on http://localhost:8080\n", .{});

//     while (true) {
//         var conn = try server.accept();
//         defer conn.close();

//         var req = try conn.receiveRequest();
//         var res = conn.response();

//         if (req) |request| {
//             try router(&handlers, request, &res);
//         } else {
//             res.status = .bad_request;
//             try res.send("Malformed request");
//         }
//     }
// }
//////////////////////////////////////////////////////////////////////////////////////////

