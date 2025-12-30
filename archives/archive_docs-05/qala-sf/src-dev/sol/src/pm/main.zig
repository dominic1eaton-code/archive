// const std = @import("std");
// const install = @import("install.zig");

// pub fn main() !void {
//     const allocator = std.heap.page_allocator;

//     const args = std.process.args();
//     if (args.len < 2) {
//         std.debug.print("Usage: mypm <package>\n", .{});
//         return;
//     }

//     const pkg = args[1];
//     try install.installPackage(allocator, pkg);

//     std.debug.print("Installed package: {s}\n", .{pkg});
// }

const std = @import("std");
const install = @import("install.zig");

pub fn main() !void {
    const allocator = std.heap.page_allocator;
    const args = std.process.args();

    if (args.len < 2) {
        std.debug.print("Usage: mypm <package>\n", .{});
        return;
    }

    const packageName = args[1];
    try install.installPackage(allocator, packageName);
}
