// @license("MIT")
// @brief("")
// @author("qala development team")
// @copyright("2024 qala development team")
const std = @import("std");
const Toolchain = @import("toolchain.zig").Toolchain;
pub fn injectToolchainIntoEnv(
    allocator: std.mem.Allocator,
    base_env: *std.ArrayList([]const u8),
    tc: Toolchain,
) !void {
    // Construct PATH
    var path_builder = std.ArrayList([]const u8).init(allocator);
    defer path_builder.deinit();

    for (tc.tools) |tool| {
        const bin = try std.fs.path.join(allocator, &[_][]const u8{ tool.path, "bin" });
        try path_builder.append(bin);
    }

    const path = try std.mem.join(allocator, ":", path_builder.items);
    try base_env.append(try std.fmt.allocPrint(allocator, "PATH={s}", .{path}));

    // Hermetic sysroot
    for (tc.tools) |tool| {
        if (std.mem.eql(u8, tool.name, "sysroot")) {
            const libp = try std.fs.path.join(allocator, &[_][]const u8{ tool.path, "lib" });
            const incp = try std.fs.path.join(allocator, &[_][]const u8{ tool.path, "include" });

            try base_env.append(try std.fmt.allocPrint(allocator, "C_INCLUDE_PATH={s}", .{incp}));
            try base_env.append(try std.fmt.allocPrint(allocator, "LIBRARY_PATH={s}", .{libp}));
            try base_env.append(try std.fmt.allocPrint(allocator, "LD_LIBRARY_PATH={s}", .{libp}));
        }
    }

    // Force Zig to use its hermetic global cache inside workspace
    try base_env.append("ZIG_GLOBAL_CACHE_DIR=.zig-cache");
}
