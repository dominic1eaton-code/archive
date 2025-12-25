const std = @import("std");
const Config = @import("config").Config;

pub fn main() !void {
    const allocator = std.heap.page_allocator;

    var config = try Config.loadTOML("config.toml", allocator);

    const db_host = config.getString("database.host") orelse "localhost";
    const ports_val = config.traverseNested("ports") orelse null;

    std.debug.print("DB Host: {s}\n", .{db_host});
    if (ports_val) |p| {
        std.debug.print("Ports: ", .{});
        for (p.Array) |port| {
            if (port.tag == .Int) std.debug.print("{d} ", .{port.Int});
        }
        std.debug.print("\n", .{});
    }

    // Modify a value
    try config.setString("database.host", "192.168.1.100");
    try config.saveTOML();
}
