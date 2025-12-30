// CLI logic
const std = @import("std");
const EnvManager = @import("env.zig").EnvManager;
const plugin = @import("plugin.zig");
const shim = @import("shim.zig");

pub fn install(env: *EnvManager, args: [][]u8) !void {
    if (args.len < 4) return error.InvalidArgument;
    const tool = args[2];
    const version = args[3];
    const url = args[4]; // Plugin must provide URL

    try env.install(tool, version, url);

    // Create shim
    const bin_path = try std.fmt.allocPrint(env.allocator, "{s}/{s}/{s}/bin/{s}", .{ ".envmgr/cache", tool, version, tool });
    try shim.createShim(env.allocator, tool, bin_path);
    std.debug.print("Installed {s} {s}\n", .{ tool, version });
}

pub fn use(env: *EnvManager, args: [][]u8) !void {
    if (args.len < 4) return error.InvalidArgument;
    const tool = args[2];
    const version = args[3];
    try env.setActive(tool, version);
    std.debug.print("Using {s} {s}\n", .{ tool, version });
}

pub fn list(env: *EnvManager) !void {
    var it = env.entries.iterator();
    while (it.next()) |entry| {
        std.debug.print("{s} → {s}\n", .{ entry.key_ptr.*, entry.value_ptr.* });
    }
}
pub const error = struct {
    InvalidArgument: error{},
};
// Note: The above code snippets are illustrative and may require additional error handling and refinements for