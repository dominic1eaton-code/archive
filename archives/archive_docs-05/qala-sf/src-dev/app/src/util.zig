const std = @import("std");

pub fn envmgrDir(allocator: *std.mem.Allocator) ![]u8 {
    const home = if (std.os.windows()) std.os.getenv("APPDATA") else std.os.getenv("HOME");
    if (home == null) return error.NoHome;
    return std.fmt.allocPrint(allocator, "{s}/.envmgr", .{home.?});
}

pub fn cacheDir(allocator: *std.mem.Allocator) ![]u8 {
    const base = try envmgrDir(allocator);
    return std.fmt.allocPrint(allocator, "{s}/cache", .{base});
}

pub fn pluginsDir(allocator: *std.mem.Allocator) ![]u8 {
    const base = try envmgrDir(allocator);
    return std.fmt.allocPrint(allocator, "{s}/plugins", .{base});
}

pub fn shimsDir(allocator: *std.mem.Allocator) ![]u8 {
    const base = try envmgrDir(allocator);
    return std.fmt.allocPrint(allocator, "{s}/shims", .{base});
}

pub const error = struct {
    NoHome: error{},
};
