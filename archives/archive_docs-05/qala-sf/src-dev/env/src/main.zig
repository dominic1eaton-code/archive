// @license("MIT")
// @brief("")
// @author("qala development team")
// @copyright("2024 qala development team")
const std = @import("std");
const Config = @import("config.zig").Config;
const env = @import("env.zig");

pub fn main() !void {
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    defer _ = gpa.deinit();

    const alloc = gpa.allocator();
    var args = std.process.args();

    _ = args.skip(); // program name

    const cmd = args.next() orelse {
        std.debug.print("usage: devcfg [apply|show] [cfg_path]\n", .{});
        return;
    };

    const cfg_path = args.next() orelse "configs/default.cfg";

    var cfg = Config.init(alloc);
    defer cfg.deinit();

    try cfg.load(cfg_path);

    if (std.mem.eql(u8, cmd, "show")) {
        for (cfg.sections.items) |s| {
            std.debug.print("[{s}]\n", .{s.name});
            for (s.entries.items) |e| {
                std.debug.print("  {s} = {s}\n", .{ e.name, e.value });
            }
        }
    } else if (std.mem.eql(u8, cmd, "apply")) {
        try env.apply(&cfg);
        std.debug.print("Environment applied.\n", .{});
    } else {
        std.debug.print("Unknown command '{s}'\n", .{cmd});
    }
}
