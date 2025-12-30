// @license("MIT")
// @brief("")
// @author("qala development team")
// @copyright("2024 qala development team")
const std = @import("std");
const Config = @import("config.zig").Config;

pub fn apply(cfg: *Config) !void {
    var env = std.process.env_map;

    // Apply environment variables
    for (cfg.sections.items) |sec| {
        if (std.mem.eql(u8, sec.name, "environment")) {
            for (sec.entries.items) |e| {
                try env.put(e.name, e.value);
            }
        }
    }

    // Optionally extend PATH or toolchain paths
    if (cfg.get("paths", "lib")) |lib| {
        try env.put("LIB_PATH", lib);
    }

    if (cfg.get("paths", "include")) |inc| {
        try env.put("INCLUDE_PATH", inc);
    }
}
