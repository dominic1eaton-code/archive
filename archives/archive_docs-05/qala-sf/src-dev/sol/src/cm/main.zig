const std = @import("std");
const Release = @import("release.zig").Release;
const storage = @import("storage.zig");

pub fn main() !void {
    const allocator = std.heap.page_allocator;
    const args = std.process.args();
    if (args.len < 2) {
        std.debug.print("Usage: release_manager [create|list|deploy|rollback]\n", .{});
        return;
    }

    const command = args[1];
    var releases = try storage.loadReleases("releases.json", allocator);

    if (std.mem.eql(u8, command, "create")) {
        if (args.len < 5) {
            std.debug.print("Usage: release_manager create <version> <notes> <env>\n", .{});
            return;
        }
        const version = args[2];
        const notes = args[3];
        const env = if (std.mem.eql(u8, args[4], "production")) Release.Environment.Production else Release.Environment.Staging;

        const release = try Release.newRelease(version, notes, null, env, allocator);
        releases = try allocator.realloc(Release, releases, releases.len + 1);
        releases[releases.len - 1] = release;

        try storage.saveReleases("releases.json", releases, allocator);
        std.debug.print("Release {s} created.\n", .{version});
    } else if (std.mem.eql(u8, command, "list")) {
        for (releases) |r| {
            std.debug.print("{s} | {s} | {s} | {s}\n", .{ r.version, r.date, r.notes, if (r.env == .Staging) "staging" else "production" });
        }
    } else if (std.mem.eql(u8, command, "deploy")) {
        if (releases.len == 0) {
            std.debug.print("No releases to deploy.\n", .{});
            return;
        }
        const latest = releases[releases.len - 1];
        std.debug.print("Deploying {s} to {s}...\n", .{ latest.version, if (latest.env == .Staging) "staging" else "production" });
        std.debug.print("Deployment successful!\n", .{});
    } else if (std.mem.eql(u8, command, "rollback")) {
        if (releases.len < 2) {
            std.debug.print("No previous release to rollback to.\n", .{});
            return;
        }
        const rollback_release = releases[releases.len - 2];
        std.debug.print("Rolling back to {s}...\n", .{rollback_release.version});
        std.debug.print("Rollback successful!\n", .{});
    } else {
        std.debug.print("Unknown command: {s}\n", .{command});
    }
}

// pub fn main() !void {
//     const args = std.process.args();
//     if (args.len < 2) {
//         std.debug.print("Usage: release_manager [create|list] ...\n", .{});
//         return;
//     }

//     const command = args[1];

//     if (std.mem.eql(u8, command, "create")) {
//         if (args.len < 4) {
//             std.debug.print("Usage: release_manager create <version> <notes>\n", .{});
//             return;
//         }
//         const version = args[2];
//         const notes = args[3];
//         const release = try Release.newRelease(version, notes, &std.heap.page_allocator);
//         try storage.saveRelease(release, "releases.txt");
//         std.debug.print("Release {s} created.\n", .{version});
//     } else if (std.mem.eql(u8, command, "list")) {
//         try storage.listReleases("releases.txt");
//     } else {
//         std.debug.print("Unknown command: {s}\n", .{command});
//     }
// }
