const pm = @import("pm");
const std = @import("std");
const db_mod = @import("db.zig");
const api = @import("api.zig");
const auth = @import("auth.zig");

pub fn main() !void {
    const allocator = std.heap.page_allocator;

    var database = try db_mod.Db.init("artifacts.db");
    defer database.close();

    const users = &_ = [_]auth.User{
        .{ .username = "alice", .token = "secret-token-123" },
    };

    var context = api.Context{
        .db = &database,
        .auth = auth.Auth.init(users[0..]),
        .storage_dir = "storage",
    };

    // ensure storage_dir exists
    _ = std.fs.cwd().createDir(context.storage_dir,  .{}) catch {};

    var server = std.http.Server.init(.{
        .port = 8080,
    });

    defer server.deinit();

    std.log.info("Listening on http://0.0.0.0:8080", .{});
    while (true) {
        const conn = try server.accept();
        defer conn.close();

        _ = server.handleConnection(conn, &context, api.handleRequest) catch |err| {
            std.log.err("Request handling error: {any}\n", .{err});
        };
    }
}
