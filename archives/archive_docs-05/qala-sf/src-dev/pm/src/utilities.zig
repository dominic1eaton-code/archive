const std = @import("std");

pub fn hashFile(filePath: []const u8) ![32]u8 {
    const fs = std.fs.cwd();
    const file = try fs.openFile(filePath, .{});
    defer file.close();

    var sha256 = std.crypto.hash.sha256.init();
    var buf: [1024]u8 = undefined;

    while (true) {
        const n = try file.read(buf[0..]);
        if (n == 0) break;
        sha256.update(buf[0..n]);
    }

    return sha256.final();
}
