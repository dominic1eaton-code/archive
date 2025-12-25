// Dynamic shim creation
const std = @import("std");
const fs = std.fs;

pub fn createShim(allocator: *std.mem.Allocator, tool: []const u8, target: []const u8) !void {
    const shims = try std.fs.cwd().createDir("shims", .{});
    defer shims.close();
    const path = try shims.createFile(tool, .{});
    defer path.close();

    const content = if (std.os.windows())
        std.fmt.allocPrint(allocator, "@echo off\r\n\"{s}\" %*\r\n", .{target})
    else
        std.fmt.allocPrint(allocator, "#!/bin/sh\n\"{s}\" \"$@\"\n", .{target});

    try path.writeAll(content);
    if (!std.os.windows()) {
        try std.os.chmod(path.path, 0o755);
    }
}
