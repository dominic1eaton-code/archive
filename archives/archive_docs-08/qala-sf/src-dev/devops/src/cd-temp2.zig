const std = @import("std");

const JobStatus = enum {
    Pending,
    Running,
    Success,
    Failure,
    Timeout,
};

const Job = struct {
    id: u32,
    name: []const u8,
    command: []const u8,
    status: JobStatus,
    retries: u8,
    dependencies: std.ArrayList(u32),
    timeout_sec: u64,
    log_file: []const u8,
};

const Pipeline = struct {
    jobs: std.ArrayList(Job>,
    allocator: *std.mem.Allocator,
    max_concurrent: usize,

    pub fn init(allocator: *std.mem.Allocator, max_concurrent: usize) Pipeline {
        return Pipeline{
            .jobs = std.ArrayList(Job).init(allocator),
            .allocator = allocator,
            .max_concurrent = max_concurrent,
        };
    }

    pub fn loadFromJSON(self: *Pipeline, file_path: []const u8) !void {
        var file = try std.fs.cwd().openFile(file_path, .{ .read = true });
        defer file.close();

        const json_str = try file.readToEndAlloc(self.allocator, 8192);
        defer self.allocator.free(json_str);

        var parser = std.json.Parser.init(json_str);
        const root = try parser.parseRoot();

        const jobs_array = try root.Object().?["jobs"].Array() catch |e| {
            return error("Invalid JSON: missing jobs array");
        };

        for (jobs_array) |job_val| {
            const obj = try job_val.Object();
            const id = @intFromU64(u32, try obj["id"].Int());
            const name = try obj["name"].String();
            const cmd = try obj["command"].String();
            const retries = @intFromU64(u8, try obj["retries"].Int());
            const timeout = try obj["timeout_sec"].Int();
            const deps_arr = try obj["dependencies"].Array() catch &.{};
            var deps = std.ArrayList(u32).init(self.allocator);
            for (deps_arr) |dep_val| try deps.append(@intFromU64(u32, dep_val.Int()));
            const log_file = try obj["log_file"].String();

            const job = Job{
                .id = id,
                .name = name,
                .command = cmd,
                .status = .Pending,
                .retries = retries,
                .dependencies = deps,
                .timeout_sec = @intFromU64(u64, timeout),
                .log_file = log_file,
            };
            try self.jobs.append(job);
        }
    }

    fn canRun(self: *Pipeline, job: *Job) bool {
        for (job.dependencies.items) |dep_id| {
            for (self.jobs.items) |j| {
                if (j.id == dep_id and j.status != .Success) return false;
            }
        }
        return true;
    }

    fn notify(job: *Job) void {
        var stdout = std.io.getStdOut().writer();
        switch (job.status) {
            .Success => _ = stdout.print("[NOTIFY] Job {s} completed successfully!\n", .{job.name}),
            .Failure => _ = stdout.print("[NOTIFY] Job {s} FAILED!\n", .{job.name}),
            .Timeout => _ = stdout.print("[NOTIFY] Job {s} TIMED OUT!\n", .{job.name}),
            else => {},
        }
    }

    fn runJob(self: *Pipeline, job: *Job) async void {
        var stdout = std.io.getStdOut().writer();
        var allocator = self.allocator;

        job.status = .Running;
        _ = stdout.print("Starting job: {s}\n", .{job.name});

        const log_path = job.log_file;
        var log_file = try std.fs.cwd().createFile(log_path, .{ .write = true, .truncate = true });
        defer log_file.close();

        var attempt: u8 = 0;
        while (attempt <= job.retries) : (attempt += 1) {
            var child = try std.ChildProcess.init(allocator);
            defer child.deinit();

            try child.setArgv(&.{ job.command });

            const stdout_pipe = try child.stdoutReader();
            const stderr_pipe = try child.stderrReader();

            try child.spawn();

            var stdout_buf: [1024]u8 = undefined;
            var stderr_buf: [1024]u8 = undefined;

            const start_time = std.time.milliTimestamp();
            var finished: bool = false;

            while (!finished) {
                // Timeout check
                const elapsed = std.time.milliTimestamp() - start_time;
                if (elapsed / 1000 > job.timeout_sec) {
                    try child.kill();
                    job.status = .Timeout;
                    _ = log_file.writeAll("Job timed out!\n");
                    notify(job);
                    return;
                }

                // Read stdout
                const out_read = try stdout_pipe.read(&stdout_buf);
                if (out_read > 0) try log_file.writeAll(stdout_buf[0..out_read]);

                // Read stderr
                const err_read = try stderr_pipe.read(&stderr_buf);
                if (err_read > 0) try log_file.writeAll(stderr_buf[0..err_read]);

                if (!child.isRunning()) finished = true;
            }

            const result = try child.wait();
            if (result == 0) {
                job.status = .Success;
                try log_file.writeAll("Job succeeded!\n");
                notify(job);
                return;
            } else if (attempt <= job.retries) {
                try log_file.writeAll("Job failed, retrying...\n");
            } else {
                job.status = .Failure;
                try log_file.writeAll("Job failed after retries!\n");
                notify(job);
            }
        }
    }

    pub fn run(self: *Pipeline) !void {
        var active_jobs: std.ArrayList(async void> = std.ArrayList(async void).init(self.allocator);

        while (true) {
            var progress = false;

            for (self.jobs.items) |*job| {
                if (job.status == .Pending and self.canRun(job) and active_jobs.items.len < self.max_concurrent) {
                    progress = true;
                    try active_jobs.append(self.runJob(job)());
                }
            }

            if (!progress) {
                if (active_jobs.items.len == 0) break;
                const finished = try active_jobs.items[0].await;
                _ = active_jobs.pop();
            }
        }
    }

    pub fn report(self: *Pipeline) void {
        var stdout = std.io.getStdOut().writer();
        _ = stdout.print("\nPipeline report:\n", .{});
        for (self.jobs.items) |job| {
            _ = stdout.print("Job {s}: {s} (log: {s})\n", .{job.name,
                switch (job.status) {
                    .Pending => "Pending",
                    .Running => "Running",
                    .Success => "Success",
                    .Failure => "Failure",
                    .Timeout => "Timeout",
                }, job.log_file});
        }
    }
};

pub fn main() !void {
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    const allocator = &gpa.allocator;

    const max_parallel_jobs = 2;
    var pipeline = Pipeline.init(allocator, max_parallel_jobs);

    try pipeline.loadFromJSON("pipeline.json");

    try pipeline.run();
    pipeline.report();
}
const std = @import("std");
const crypto = std.crypto;
const fs = std.fs;
const path = std.fs.path;
const Job = @import("cd-temp.zig").Job;
const CacheResult = enum {
    Hit,
    Miss,
};
pub fn computeJobHash(
    allocator: std.mem.Allocator,
    job: Job,
    dependencies: [][]const u8,
) ![]u8 {
    var hasher = crypto.hash.SHA256.init();
    hasher.update(job.name);
    hasher.update(job.command);
    for (dependencies) |dep| {
        hasher.update(dep);
    }
    const digest = hasher.final();
    var out = try allocator.alloc(u8, digest.len);
    std.mem.copy(u8, out, digest[0..]);
    return out;
}
pub fn cacheDir(allocator: std.mem.Allocator, job_name: []const u8) ![]const u8 {
    return try path.join(allocator, &[_][]const u8{
        ".ci_cache", "jobs", job_name,
    });
}
pub fn checkCache(
    allocator: std.mem.Allocator,
    job: Job,
    hash: []const u8,
) !CacheResult {
    const dir = try cacheDir(allocator, job.name);
    var cwd = fs.cwd();
    var cache = cwd.openDir(dir, .{}) catch return CacheResult.Miss;
    defer cache.close();
    const hash_path = "hash";
    const stored = cache.readFileAlloc(allocator, hash_path, 1024) catch return CacheResult.Miss;
    if (std.mem.eql(u8, stored, hash))
        return CacheResult.Hit;
    return CacheResult.Miss;
}
pub fn storeCache(
    allocator: std.mem.Allocator,
    job: Job,
    hash: []const u8,
    artifact_paths: [][]const u8,
) !void {
    const dir = try cacheDir(allocator, job.name);
    var cwd = fs.cwd();
    try cwd.createDirAll(dir, 0o755);
    var cache = cwd.openDir(dir, .{ .write = true }) catch |err| {
        return err;
    };
    defer cache.close();
    const hash_path = "hash";
    var hash_file = try cache.createFile(hash_path, .{ .write = true, .truncate = true });
    defer hash_file.close();
    try hash_file.writeAll(hash);
    for (artifact_paths) |artifact_path| {
        const file_name = path.basename(artifact_path);
        const dest_path = try path.join(allocator, &[_][]const u8{ dir, file_name });
        defer allocator.free(dest_path);
        try fs.cwd().copyFile(artifact_path, dest_path);
    }
}
pub fn tryLoadFromCache(
    allocator: std.mem.Allocator,
    job: Job,
    hash: []const u8,
    dest_dir: []const u8,
) !bool {
    const dir = try cacheDir(allocator, job.name);
    var cwd = fs.cwd();
    var cache = cwd.openDir(dir, .{}) catch return false;
    defer cache.close();
    const hash_path = "hash";
    const stored = cache.readFileAlloc(allocator, hash_path, 1024) catch return false;
    if (!std.mem.eql(u8, stored, hash)) {
        return false;
    }
    const entries = try cache.readDir();
    for (entries) |entry| {
        if (entry.name == "hash") continue;
        const src_path = try path.join(allocator, &[_][]const u8{ dir, entry.name });
        defer allocator.free(src_path);
        const dest_path = try path.join(allocator, &[_][]const u8{ dest_dir, entry.name });
        defer allocator.free(dest_path);
        try cwd.copyFile(src_path, dest_path);
    }
    return true;
}
pub fn computeDependenciesHash(
    allocator: std.mem.Allocator,
    dependencies: [][]const u8,
) ![]const u8 {
    var hasher = std.crypto.hash.SHA256.init();
    for (dependencies) |dep_path| {
        const file_data = try std.fs.cwd().readFileAlloc(allocator, dep_path, 1024 * 1024);
        hasher.update(file_data);
        allocator.free(file_data);
    }
    const digest = hasher.finalResult();
    var out = try allocator.alloc(u8, digest.len);
    std.mem.copy(u8, out, digest[0..]);
    return out;
}
pub fn computeJobHash(
    allocator: std.mem.Allocator,
    job: Job,
) ![]u8 {
    var hasher = std.crypto.hash.SHA256.init();
    hasher.update(job.name);
    hasher.update(job.command);
    const dependencies = try computeDependenciesHash(allocator, &[_][]const u8{});
    for (dependencies) |dep| {
        hasher.update(dep);
    }
    const digest = hasher.final();
    var out = try allocator.alloc(u8, digest.len);
    std.mem.copy(u8, out, digest[0..]);
    return out;
}
pub fn computeJobHashWithDeps(
    allocator: std.mem.Allocator,
    job: Job,
    dependencies: [][]const u8,
) ![]u8 {
    var hasher = std.crypto.hash.SHA256.init();
    hasher.update(job.name);
    hasher.update(job.command);
    for (dependencies) |dep| {
        hasher.update(dep);
    }
    const digest = hasher.final();
    var out = try allocator.alloc(u8, digest.len);
    std.mem.copy(u8, out, digest[0..]);
    return out;
}


