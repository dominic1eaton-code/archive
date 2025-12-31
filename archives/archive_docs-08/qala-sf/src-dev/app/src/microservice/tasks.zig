const std = @import("std");
const Db = @import("db.zig").Db;

pub fn processAppEvent(db: *Db, event_json: []const u8) !void {
    // parse JSON: {"id":123,"name":"app","version":"1.0"}
    const obj = try std.json.parse(event_json, std.heap.page_allocator);
    defer obj.deinit();

    const id = obj.Object.get("id") orelse return error.InvalidEvent;
    try db.markAppProcessed(@intCast(u32, id.Integer));
}
