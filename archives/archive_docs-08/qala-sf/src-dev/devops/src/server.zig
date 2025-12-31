const std = @import("std");
const Hub = @import("websocket.zig").WebsocketHub;

pub fn startServer(allocator: *std.mem.Allocator, hub: *Hub) !void {
    var server = try std.net.StreamServer.listen(allocator, "0.0.0.0", 8080);
    defer server.deinit();

    while (true) {
        const conn = try server.accept();
        async handleConnection(allocator, conn, hub);
    }
}

fn handleConnection(alloc: *std.mem.Allocator, conn: std.net.StreamServer.Connection, hub: *Hub) !void {
    var reader = conn.reader();
    var writer = conn.writer();

    var buf: [2048]u8 = undefined;
    const n = try reader.read(&buf);

    if (std.mem.startsWith(u8, buf[0..n], "GET /ws")) {
        // WebSocket handshake (simplified)
        try writer.writeAll(
            "HTTP/1.1 101 Switching Protocols\r\n"
            "Upgrade: websocket\r\n"
            "Connection: Upgrade\r\n\r\n"
        );

        try hub.conns.append(&conn.stream);

        while (true) {
            const r = reader.read(&buf) catch break;
            if (r > 0) {
                hub.handleMessage(pipeline, buf[0..r]);
            }
        }
        return;
    }

    // Static files
    if (std.mem.startsWith(u8, buf[0..n], "GET / ")) {
        const file = try std.fs.cwd().openFile("www/index.html", .{ .read = true });
        defer file.close();
        try writer.print("HTTP/1.1 200 OK\r\nContent-Type: text/html\r\n\r\n", .{});
        try file.copyTo(writer);
        return;
    }
}
