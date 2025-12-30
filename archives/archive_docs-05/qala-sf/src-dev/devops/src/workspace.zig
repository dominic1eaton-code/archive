// @license("MIT")
// @brief("")
// @author("qala development team")
// @copyright("2024 qala development team")
const std = @import("std");

pub fn createWorkspace(
    allocator: std.mem.Allocator,
    job_name: []const u8,
) ![]const u8 {
    const root = try std.fs.path.join(allocator, &[_][]const u8{
        ".ci_workspace",
        job_name,
    });

    var cwd = std.fs.cwd();
    // Clear workspace
    _ = cwd.deleteTree(root) catch {};
    try cwd.makePath(root);

    return root;
}

/// Extract cached artifact into workspace
pub fn mountDependencyArtifact(
    allocator: std.mem.Allocator,
    workspace: []const u8,
    dep_name: []const u8,
) !void {
    const artifact_path = try std.fs.path.join(
        allocator,
        &[_][]const u8{
            ".ci_cache", "jobs", dep_name, "artifact.tar",
        },
    );

    var cwd = std.fs.cwd();
    if (cwd.access(artifact_path, .{}) != null) return;

    // run tar -xf inside workspace
    var buf: [256]u8 = undefined;
    const cmd = try std.fmt.bufPrint(
        &buf,
        "tar -xf {s} -C {s}",
        .{ artifact_path, workspace },
    );

    var child = std.ChildProcess.init(&.{ "/bin/sh", "-c", cmd }, allocator);
    child.stdin_behavior = .Inherit;
    child.stdout_behavior = .Inherit;
    child.stderr_behavior = .Inherit;

    if (try child.spawnAndWait() != 0)
        return error.ArtifactExtractFailed;
}

/// Linux-only: enter a sandbox via unshare
pub fn enterSandbox() !void {
    const errno = std.os.linux.unshare(
        std.os.linux.CLONE.NEWUSER |
            std.os.linux.CLONE.NEWNS |
            std.os.linux.CLONE.NEWCGROUP |
            std.os.linux.CLONE.NEWPID |
            std.os.linux.CLONE.NEWIPC |
            std.os.linux.CLONE.NEWNET,
    );

    if (errno != 0) return error.SandboxUnavailable;
}
