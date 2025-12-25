// @license("MIT")
// @brief("hermetic toolchain management for qala projects")
// @author("qala development team")
// @copyright("2024 qala development team")
const std = @import("std");

pub const Tool = struct {
    name: []const u8, // "zig", "clang", "sysroot"
    version: []const u8, // "0.13.0", "17.0", "glibc-2.37"
    path: []const u8, // ".ci_toolchain/zig-0.13.0"
    targets: [][]const u8, // ← NEW e.g. ["x86_64-linux-gnu", "aarch64-linux-gnu"]
};

pub const Toolchain = struct {
    tools: []Tool,
};

/// Load manifest from .ci_toolchain/manifest.json
pub fn load(
    allocator: std.mem.Allocator,
) !Toolchain {
    var cwd = std.fs.cwd();
    const txt = try cwd.readFileAlloc(allocator, ".ci_toolchain/manifest.json", 64 * 1024);

    var parser = std.json.Parser.init(allocator, false);
    defer parser.deinit();

    const root = try parser.parse(txt);
    const arr = root.object.get("tools").?.array;

    var list = std.ArrayList(Tool).init(allocator);

    for (arr.items) |entry| {
        try list.append(.{
            .name = entry.object.get("name").?.string,
            .version = entry.object.get("version").?.string,
            .path = entry.object.get("path").?.string,
        });
    }

    return Toolchain{ .tools = try list.toOwnedSlice() };
}

pub fn injectTarget(
    allocator: std.mem.Allocator,
    env_list: *std.ArrayList([]const u8),
    tc: Toolchain,
    target: []const u8,
) !void {
    for (tc.tools) |tool| {
        for (tool.targets) |tgt| {
            if (std.mem.eql(u8, tgt, target)) {
                // target sysroot
                if (std.mem.eql(u8, tool.name, "sysroot")) {
                    const libp = try std.fs.path.join(allocator, &[_][]const u8{
                        tool.path, "lib", target,
                    });
                    const incp = try std.fs.path.join(allocator, &[_][]const u8{
                        tool.path, "include", target,
                    });

                    try env_list.append(try std.fmt.allocPrint(allocator, "C_INCLUDE_PATH={s}", .{incp}));
                    try env_list.append(try std.fmt.allocPrint(allocator, "LIBRARY_PATH={s}", .{libp}));
                    try env_list.append(try std.fmt.allocPrint(allocator, "LD_LIBRARY_PATH={s}", .{libp}));
                }
            }
        }
    }

    // Zig target flag
    try env_list.append(try std.fmt.allocPrint(allocator, "ZIG_TARGET={s}", .{target}));
}
