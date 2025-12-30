const std = @import("std");
const Handlers = @import("handlers.zig").Handlers;

pub fn route(handlers: *Handlers, req: *std.http.Server.Request, res: *std.http.Server.Response) !void {
    if (std.mem.eql(u8, req.path, "/apps") and req.method == .GET) {
        return handlers.listApps(res);
    }

    if (std.mem.eql(u8, req.path, "/apps") and req.method == .POST) {
        return handlers.createApp(req, res);
    }

    res.status = .not_found;
    try res.send("Not Found");
}
