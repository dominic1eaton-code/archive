const std = @import("std");
const fs = std.fs;


// We can use std.fs and std.io for downloads and extraction. Zig does not have native tar/zip support yet, but we can:
// Use curl/wget as subprocess for downloading.
// Use tar/unzip CLI for extraction (cross-platform).
// Or implement minimal .tar.gz parsing using std.compress.
pub fn downloadAndExtract(url: []const u8, target_dir: []const u8) !void {
    const allocator = std.heap.page_allocator;

    // Download to temp file
    const tmp_file = try fs.cwd().createFile("tmp_download", .{});
    defer tmp_file.close();

    const cmd = &[_][]const u8{"curl", "-L", url, "-o", "tmp_download"};
    const result = try std.ChildProcess.init(allocator)
        .spawn(.{ .argv = cmd }) catch unreachable;
    _ = try result.wait();
    
    // Determine archive type
    if (std.mem.endsWith(u8, url, ".tar.gz") or std.mem.endsWith(u8, url, ".tgz")) {
        _ = try std.ChildProcess.init(allocator)
            .spawn(.{ .argv = &[_][]const u8{"tar", "-xzf", "tmp_download", "-C", target_dir} })
            ?.wait();
    } else if (std.mem.endsWith(u8, url, ".zip")) {
        _ = try std.ChildProcess.init(allocator)
            .spawn(.{ .argv = &[_][]const u8{"unzip", "tmp_download", "-d", target_dir} })
            ?.wait();
    } else {
        return error.UnsupportedArchive;
    }

    try fs.cwd().removeFile("tmp_download");
}
pub const error = struct {
    UnsupportedArchive: error{},
};


// Version resolution ("latest", ranges)
// Store available versions in plugin metadata (JSON or remote URL).
// Allow keywords like "latest" → fetch highest version.
// Implement simple SemVer comparison.
pub fn resolveVersion(available: [][]const u8, requested: []const u8) ![]const u8 {
    if (std.mem.eql(u8, requested, "latest")) {
        var latest = available[0];
        for (available) |v| {
            if (compareSemVer(v, latest) > 0) latest = v;
        }
        return latest;
    }
    // TODO: implement ranges like "^1.2.0"
    return requested;
}

fn compareSemVer(a: []const u8, b: []const u8) i32 {
    const split = std.mem.split(u8, a, ".");
    const splitB = std.mem.split(u8, b, ".");
    for (0..3) |i| {
        const ai = std.fmt.parseInt(u32, split[i], 10) catch 0;
        const bi = std.fmt.parseInt(u32, splitB[i], 10) catch 0;
        if (ai < bi) return -1;
        if (ai > bi) return 1;
    }
    return 0;
}

// Per-project .envmgr file
// Similar to .tool-versions in asdf.
// Each project can define tool + version mappings.
// Load at runtime by searching parent directories.
pub fn findProjectConfig(allocator: *std.mem.Allocator) !?[]u8 {
    var dir = try std.fs.cwd().openDir(".");
    while (true) {
        const path = try std.fmt.allocPrint(allocator, "{s}/.envmgr", .{dir.path});
        if (try std.fs.cwd().exists(path)) return path;
        if (dir.path == "/") break;
        dir.path = std.fs.pathDir(dir.path); // go up one level
    }
    return null;
}


// Shims (like asdf/mise)
// Create executables that forward calls to the correct version of the tool.
// Can be installed in $HOME/.envmgr/shims or APPDATA\envmgr\shims.
pub fn createShim(tool: []const u8, version: []const u8) !void {
    const shim_path = try std.fs.cwd().createFile("{tool}", .{});
    try shim_path.writeAll("Zig shim exec code here pointing to correct tool version");
}

// Plugin system (envmgr plugin add nodejs)
// Plugins are JSON/YAML files describing:
// Available versions
// Download URLs
// Install scripts
// Store in $HOME/.envmgr/plugins/nodejs.json
// Load dynamically at runtime to install/use tools.
pub fn addPlugin(name: []const u8, url: []const u8) !void {
    // Save plugin metadata to ~/.envmgr/plugins/{name}.json
}

// Caching + lockfiles
// Cache downloads in ~/.envmgr/cache/{tool}/{version}
// Generate .envmgr.lock per project to lock versions.
// Before installing, check if cached archive exists.
pub fn getCachedArchive(tool: []const u8, version: []const u8) !?[]const u8 {
    const path = try std.fmt.allocPrint(allocator, "~/.envmgr/cache/{s}/{s}.tar.gz", .{tool, version});
    if (try std.fs.cwd().exists(path)) return path;
    return null;
}

// Windows compatibility via APPDATA
// $APPDATA/envmgr instead of ~/.envmgr
// Use std.os.getenv("APPDATA") instead of HOME on Windows.
pub fn envmgrPath(allocator: *std.mem.Allocator) ![]u8 {
    var base = std.os.getenv("HOME");
    if (std.os.windows()) {
        base = std.os.getenv("APPDATA") orelse return error.NoHome;
    } else {
        base = base orelse return error.NoHome;
    }
    return std.fmt.allocPrint(allocator, "{s}/.envmgr", .{base});
}
pub const error = struct {
    NoHome: error{},
};
// Note: The above code snippets are illustrative and may require additional error handling and refinements for production use.