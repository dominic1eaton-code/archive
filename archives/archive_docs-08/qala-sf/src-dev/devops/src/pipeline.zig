// @license("MIT")
// @brief("")
// @author("qala development team")
// @copyright("2024 qala development team")
const std = @import("std");
const Job = @import("build.zig").Job;
const JobResult = @import("build.zig").JobResult;
const Config = @import("config.zig").Config;
const runJob = @import("executor.zig").runJob;

pub const PipelineJob = struct {
    job: Job,
    deps: [][]const u8,
};

pub const Pipeline = struct {
    jobs: []PipelineJob,

    pub fn run(self: *Pipeline, allocator: std.mem.Allocator) !void {
        var completed = std.StringHashMap(JobResult).init(allocator);
        defer completed.deinit();

        while (completed.count() < self.jobs.len) {
            var progress = false;

            for (self.jobs) |pj| {
                if (completed.contains(pj.job.name)) continue;

                // Check dependencies
                var deps_ok = true;
                for (pj.deps) |dep| {
                    if (!completed.contains(dep)) {
                        deps_ok = false;
                        break;
                    }
                    if (completed.get(dep).? == JobResult.failed) {
                        std.debug.print("Dependency failed: {s}\n", .{ dep });
                        return;
                    }
                }
                if (!deps_ok) continue;

                // Run job
                std.debug.print("▶ Running job: {s}\n", .{pj.job.name});
                const result = try pj.job.run(allocator);
                std.debug.print("■ Job {s}: {s}\n",
                    .{pj.job.name, result == .success ? "SUCCESS" : "FAIL"});

                try completed.put(pj.job.name, result);
                progress = true;
            }

            if (!progress) return error.CircularDependency;
        }
    }
};

pub fn runPipeline(cfg: Config, allocator: std.mem.Allocator) !void {
    const stdout = std.io.getStdOut().writer();
    try stdout.print("Starting pipeline...\n", .{});

    var threads = std.ArrayList(std.Thread).init(allocator);

    for (cfg.pipeline.jobs) |job| {
        const thread = try std.Thread.spawn(.{}, runJob, .{ job, allocator });
        try threads.append(thread);
    }

    for (threads.items) |t| {
        t.join();
    }

    try stdout.print("Pipeline finished.\n", .{});
}

pub const error = error{ CircularDependency };

//////////////////////////////////////////////////////////////////////

pub const JobStatus = enum {
    Pending,
    Running,
    Success,
    Failure,
    Timeout,
    Manual,
};

pub const Job = struct {
    id: u32,
    name: []const u8,
    command: []const u8,
    retries: u8,
    timeout_sec: u64,
    dependencies: []u32,
    status: JobStatus,
    log: std.ArrayList(u8),
};

pub const Pipeline = struct {
    allocator: *std.mem.Allocator,
    jobs: std.ArrayList(Job),
    max_parallel: usize,

    pub fn init(allocator: *std.mem.Allocator, max_parallel: usize) Pipeline {
        return .{
            .allocator = allocator,
            .jobs = std.ArrayList(Job).init(allocator),
            .max_parallel = max_parallel,
        };
    }

    pub fn getJobById(self: *Pipeline, id: u32) ?*Job {
        for (self.jobs.items) |*j| if (j.id == id) return j;
        return null;
    }

    pub fn appendLog(job: *Job, text: []const u8) void {
        job.log.appendSlice(text) catch {};
    }

    fn canRun(self: *Pipeline, job: *Job) bool {
        for (job.dependencies) |dep|
            if (self.getJobById(dep).?.status != .Success)
                return false;
        return true;
    }

    pub fn trigger(self: *Pipeline, job_id: u32) !void {
        const job = self.getJobById(job_id) orelse return error.JobNotFound;
        job.status = .Manual;
    }

    pub fn runJob(self: *Pipeline, job: *Job) anyerror!void {
        job.status = .Running;
        appendLog(job, "Starting job...\n");

        var attempt: u8 = 0;
        while (attempt <= job.retries) : (attempt += 1) {
            var child = try std.ChildProcess.init(self.allocator);
            defer child.deinit();

            try child.setArgv(&.{ job.command });
            const so = try child.stdoutReader();
            const se = try child.stderrReader();

            try child.spawn();

            var buf: [512]u8 = undefined;
            const start = std.time.milliTimestamp();

            while (child.isRunning()) {
                if ((std.time.milliTimestamp() - start) / 1000 > job.timeout_sec) {
                    try child.kill();
                    job.status = .Timeout;
                    appendLog(job, "Timeout\n");
                    return;
                }

                const r = so.read(&buf) catch 0;
                if (r > 0) appendLog(job, buf[0..r]);

                const e = se.read(&buf) catch 0;
                if (e > 0) appendLog(job, buf[0..e]);

                std.time.sleep(50_000_000); // 50ms
            }

            const code = try child.wait();
            if (code == 0) {
                job.status = .Success;
                appendLog(job, "Success\n");
                return;
            }
            appendLog(job, "Attempt failed\n");
        }

        job.status = .Failure;
        appendLog(job, "Job failed after retries\n");
    }
};
pub const error = error{
    JobNotFound,
};
