const std = @import("std");
const http = std.http;

pub fn startServer() !void {
    const allocator = std.heap.page_allocator;
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    const listener = try std.net.StreamServer.listen(.{
        .address = .{ .ip = "0.0.0.0", .port = 8080 },
    });
    defer listener.close();

    while (true) {
        const conn = try listener.accept();
        _ = handleConnection(&conn) catch {};
        conn.close() catch {};
    }
}

fn handleConnection(conn: *std.net.StreamServer.Connection) !void {
    var buffer: [1024]u8 = undefined;
    const r = try conn.reader().read(buffer[0..]);
    // Very naive HTTP parser; expand as needed
    if (r > 0) {
        const response = "HTTP/1.1 200 OK\r\nContent-Length: 2\r\n\r\nOK";
        try conn.writer().writeAll(response);
    }
}

const std = @import("std");
const http = std.http;

pub fn startServer() !void {
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    defer gpa.deinit();

    var server = http.Server(.{}){};
    try server.listen(.{ .port = 8080 });
    while (true) {
        const conn = try server.accept();
        defer conn.close();
        _ = handleConnection(&conn) catch {};
    }
}

fn handleConnection(conn: *http.ServerConnection) !void {
    var req = try conn.readRequest();
    try handleRequest(&req);
    try conn.sendResponse(.{ .status = .ok, .body = "OK" });
}

fn handleRequest(req: *http.Request) !void {
    const path = req.path;
    if (std.mem.startsWith(path, "/upload")) {
        try handleUpload(req);
    } else if (std.mem.startsWith(path, "/download")) {
        try handleDownload(req);
    } else if (std.mem.startsWith(path, "/search")) {
        try handleSearch(req);
    } else {
        try send404(req);
    }
}

// fn handleRequest(req: *http.Request) !void {
//     // Handle different routes and methods here
//     switch (req.method) {
//         .get => {
//             // Handle GET request
//         },
//         .post => {
//             // Handle POST request
//         },
//         else => {},
//     }
// }
