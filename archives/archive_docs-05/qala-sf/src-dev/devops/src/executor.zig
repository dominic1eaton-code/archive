// @license("MIT")
// @brief("")
// @author("qala development team")
// @copyright("2024 qala development team")
const std = @import("std");
const Job = @import("config.zig").Job;
const tc = try toolchain.load(allocator);
var env_list = std.ArrayList([]const u8).init(allocator);

pub fn runJobWithArtifacts(
    job: Job,
    allocator: std.mem.Allocator,
    artifact_path: []const u8,
) !void {
    const stdout = std.io.getStdOut().writer();

    try stdout.print("== Running job: {s}\n", .{job.name});

    // run steps (same as before)
    for (job.steps) |step| {
        try stdout.print(" → Exec: {s}\n", .{step.command});

        var child = std.ChildProcess.init(&.{ "/bin/sh", "-c", step.command }, allocator);
        child.stdin_behavior = .Inherit;
        child.stdout_behavior = .Inherit;
        child.stderr_behavior = .Inherit;

        if (try child.spawnAndWait() != 0)
            return error.StepFailed;
    }

    // Create artifact tarball
    {
        var cmd_buf: [256]u8 = undefined;
        const cmd = try std.fmt.bufPrint(
            &cmd_buf,
            "tar -czf {s} ./zig-out",
            .{artifact_path},
        );

        var child = std.ChildProcess.init(&.{ "/bin/sh", "-c", cmd }, allocator);
        child.stdin_behavior = .Inherit;
        child.stdout_behavior = .Inherit;
        child.stderr_behavior = .Inherit;

        if (try child.spawnAndWait() != 0)
            return error.ArtifactError;

        // Use Hermetic Toolchain
        try envlock.applyDeterministicDefaults(allocator, &env_list);

        // inject hermetic toolchain paths
        try injectToolchainIntoEnv(allocator, &env_list, tc);

        child.env_map = .{ .entries = try env_list.toOwnedSlice() };

        try stdout.print("✓ Artifact written: {s}\n", .{artifact_path});
    }
}

pub fn runJobIncremental(
    job: Job,
    allocator: std.mem.Allocator,
    dep_hashes: []const []const u8,
    final_artifact: []const u8,
) !void {
    const ws_mod = @import("workspace.zig");
    const step_cache = @import("cache_step.zig");

    const stdout = std.io.getStdOut().writer();

    const workspace = try ws_mod.createWorkspace(allocator, job.name);

    // Sandbox if supported
    ws_mod.enterSandbox() catch |err| {
        try stdout.print("(sandbox unavailable: {any})\n", .{err});
    };

    // Mount dependency artifacts
    for (job.needs) |dep| {
        try ws_mod.mountDependencyArtifact(allocator, workspace, dep);
    }

    try stdout.print("== Running job (incremental): {s}\n", .{job.name});

    // run steps one by one
    for (job.steps, 0..) |step, index| {
        const step_hash = try step_cache.computeStepHash(
            allocator,
            job.name,
            index,
            step.command,
            dep_hashes,
        );

        if (try step_cache.checkStepCache(allocator, job.name, index, step_hash)) {
            try stdout.print(" → Step {d} cache hit: {s}\n", .{ index, step.command });
            continue;
        }

        // run step inside workspace (set cwd)
        var child = std.ChildProcess.init(&.{ "/bin/sh", "-c", step.command }, allocator);
        child.cwd = workspace;
        child.stdin_behavior = .Inherit;
        child.stdout_behavior = .Inherit;
        child.stderr_behavior = .Inherit;

        if (try child.spawnAndWait() != 0)
            return error.StepFailed;

        // store step hash
        try step_cache.storeStepCache(allocator, job.name, index, step_hash);
    }

    // Final artifact creation
    var cmd_buf: [256]u8 = undefined;
    const tar_cmd = try std.fmt.bufPrint(
        &cmd_buf,
        "tar -czf {s} -C {s} .",
        .{ final_artifact, workspace },
    );

    var tar = std.ChildProcess.init(&.{ "/bin/sh", "-c", tar_cmd }, allocator);
    tar.stdin_behavior = .Inherit;
    tar.stdout_behavior = .Inherit;
    tar.stderr_behavior = .Inherit;

    if (try tar.spawnAndWait() != 0)
        return error.ArtifactError;

    // Use Hermetic Toolchain
    try envlock.applyDeterministicDefaults(allocator, &env_list);

    // inject hermetic toolchain paths
    try injectToolchainIntoEnv(allocator, &env_list, tc);

    child.env_map = .{ .entries = try env_list.toOwnedSlice() };

    try stdout.print("✓ Job artifact created for {s}\n", .{job.name});
}

const runJobIncremental = @import("executor.zig").runJobIncremental;
const runJobWithArtifacts = @import("executor.zig").runJobWithArtifacts;
pub const error = struct {
    StepFailed: error{StepFailed},
    ArtifactError: error{ArtifactError},
};