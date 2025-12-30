// @license("MIT")
// @brief("")
// @author("qala development team")
// @copyright("2024 qala development team")
const std = @import("std");
const Job = @import("config.zig").Job;

pub const JobResult = enum {
    success,
    failed,
};

//  needs = ["job1", "job2"]
pub const Job = struct {
    name: []const u8,
    command: []const u8,
    needs: [][]const u8, // ← new

    pub fn run(self: *const Job, allocator: std.mem.Allocator) !JobResult {
        const cwd = std.fs.cwd();
        var child = std.process.Child.init(&[_][]const u8{ "/bin/sh", "-c", self.command }, allocator);
        child.stdin_behavior = .Inherit;
        child.stdout_behavior = .Inherit;
        child.stderr_behavior = .Inherit;

        try child.spawn();
        const result = try child.wait();

        return if (result.Exited == 0)
            JobResult.success
        else
            JobResult.failed;
    }
};

pub fn runJobs(jobs: []const Job, allocator: std.mem.Allocator) !void {
    for (jobs) |job| {
        std.debug.print("Running job: {s}\n", .{job.name});
        const result = try job.run(allocator);
        switch (result) {
            .success => std.debug.print("Job {s} completed successfully.\n", .{job.name}),
            .failed => std.debug.print("Job {s} failed.\n", .{job.name}),
        }
    }
}

pub fn bufferedPrint() !void {
    var stdout = std.io.getStdOut().writer();
    try stdout.print("Buffered print from devops module.\n", .{});
}

pub fn runJob(job: Job, allocator: std.mem.Allocator) !void {
    const stdout = std.io.getStdOut().writer();

    try stdout.print("== Running job: {s}\n", .{job.name});

    for (job.steps) |step| {
        try stdout.print(" → Exec: {s}\n", .{step.command});

        var child = std.ChildProcess.init(&.{ "/bin/sh", "-c", step.command }, allocator);
        child.stdin_behavior = .Inherit;
        child.stdout_behavior = .Inherit;
        child.stderr_behavior = .Inherit;

        const result = try child.spawnAndWait();
        if (result != 0) {
            return error.StepFailed;
        }
    }

    try stdout.print("✓ Job {s} completed successfully\n", .{job.name});
}
