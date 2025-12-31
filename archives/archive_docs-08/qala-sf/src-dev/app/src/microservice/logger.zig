const std = @import("std");

pub fn logRequest(req: *std.http.Server.Request) void {
    std.debug.print("[{}] {} {}\n", .{
        std.time.timestamp(),
        req.method,
        req.path,
    });
}
