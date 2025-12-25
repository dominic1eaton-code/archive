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

    pub fn addJob(self: *Pipeline, id: u32, name: []const u8, command: []const u8, retries: u8, timeout_sec: u64, deps: []const u32) !void {
        var dep_list = std.ArrayList(u32).init(self.allocator);
        for (deps) |dep| try dep_list.append(dep);

        const job = Job{
            .id = id,
            .name = name,
            .command = command,
            .status = .Pending,
            .retries = retries,
            .dependencies = dep_list,
            .timeout_sec = timeout_sec,
        };
        try self.jobs.append(job);
    }

    fn canRun(self: *Pipeline, job: *Job) bool {
        for (job.dependencies.items) |dep_id| {
            for (self.jobs.items) |j| {
                if (j.id == dep_id and j.status != .Success) {
                    return false;
                }
            }
        }
        return true;
    }

    fn runJob(self: *Pipeline, job: *Job) async void {
        var stdout = std.io.getStdOut().writer();
        var allocator = self.allocator;

        job.status = .Running;
        _ = stdout.print("Starting job: {s}\n", .{job.name});

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
                // Check timeout
                const elapsed = std.time.milliTimestamp() - start_time;
                if (elapsed / 1000 > job.timeout_sec) {
                    try child.kill();
                    job.status = .Timeout;
                    _ = stdout.print("Job {s} timed out!\n", .{job.name});
                    return;
                }

                // Read stdout
                const out_read = try stdout_pipe.read(&stdout_buf);
                if (out_read > 0) {
                    _ = stdout.writeAll(stdout_buf[0..out_read]);
                }

                // Read stderr
                const err_read = try stderr_pipe.read(&stderr_buf);
                if (err_read > 0) {
                    _ = stdout.print("ERR: ", .{});
                    _ = stdout.writeAll(stderr_buf[0..err_read]);
                }

                // Check if child finished
                if (child.isRunning() == false) {
                    finished = true;
                }
            }

            const result = try child.wait();
            if (result == 0) {
                job.status = .Success;
                _ = stdout.print("Job {s} succeeded\n", .{job.name});
                return;
            } else if (attempt <= job.retries) {
                _ = stdout.print("Job {s} failed, retry {d}\n", .{job.name, attempt});
            } else {
                job.status = .Failure;
                _ = stdout.print("Job {s} failed after {d} retries\n", .{job.name, job.retries});
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
            _ = stdout.print("Job {s}: {s}\n", .{
                job.name,
                switch (job.status) {
                    .Pending => "Pending",
                    .Running => "Running",
                    .Success => "Success",
                    .Failure => "Failure",
                    .Timeout => "Timeout",
                },
            });
        }
    }
};

pub fn main() !void {
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    const allocator = &gpa.allocator;

    const max_parallel_jobs = 2;
    var pipeline = Pipeline.init(allocator, max_parallel_jobs);

    try pipeline.addJob(1, "Build", "sleep 2 && echo Building project", 1, 5, &.{});
    try pipeline.addJob(2, "Test", "sleep 3 && echo Running tests", 2, 4, &.{1}); // Depends on Build
    try pipeline.addJob(3, "Deploy", "sleep 6 && echo Deploying application", 1, 5, &.{2}); // Depends on Test
    try pipeline.addJob(4, "Lint", "sleep 1 && echo Linting code", 0, 2, &.{1}); // Depends on Build

    try pipeline.run();
    pipeline.report();
}

//     const cache = cwd.createDir(dir, .{}) catch |err| {
//         if (err != std.fs.Error.DirAlreadyExists) return err;
//     };

//     defer cache.close();

//     // store artifact
//     const artifact_dest = try std.fs.path.join(allocator, &[_][]const u8{ dir, "artifact" });
//     try std.fs.copyFile(artifact_path, artifact_dest);

//     // store hash
//     const hash_path = try std.fs.path.join(allocator, &[_][]const u8{ dir, "hash" });
//     var hash_file = try cwd.createFile(hash_path, .{});
//     defer hash_file.close();
//     try hash_file.writeAll(hash);

//     allocator.free(artifact_dest);
//     allocator.free(hash_path);
// }

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
    const digest = hasher.final();
    var out = try allocator.alloc(u8, digest.len);
    std.mem.copy(u8, out, digest[0..]);
    return out;
}

pub fn restoreCache(
    allocator: std.mem.Allocator,
    action_hash: []const u8,
    artifact_path: []const u8,
) !bool {
    const cache_result = try checkCache(allocator, Job{ .id = 0, .name = "temp", .command = "", .status = .Pending, .retries =
    0, .dependencies = std.ArrayList(u32).init(allocator), .timeout_sec = 0 }, action_hash);
    if (cache_result == CacheResult.Hit) {
        // extract artifact from cache
        const cache_dir = try cacheDir(allocator, "temp");
        const artifact_src = try std.fs.path.join(allocator, &[_][]const u8{ cache_dir, "artifact.tar" });
        try std.fs.copyFile(artifact_src, artifact_path);
        allocator.free(cache_dir);
        allocator.free(artifact_src);
        return true;
    }
    return false;
}

pub fn computeHash(
    allocator: std.mem.Allocator,
    paths: [][]const u8,
) ![]const u8 {
    var hasher = std.crypto.hash.SHA256.init();
    for (paths) |path| {
        const file_data = try std.fs.cwd().readFileAlloc(allocator, path, 1024 * 1024);
        hasher.update(file_data);
        allocator.free(file_data);
    }
    const digest = hasher.final();
    var out = try allocator.alloc(u8, digest.len);
    std.mem.copy(u8, out, digest[0..]);
    return out;
}

pub fn restoreCache(
    allocator: std.mem.Allocator,
    action_hash: []const u8,
    artifact_path: []const u8,
) !bool {
    const cache_result = try checkCache(allocator, Job{ .id = 0, .name = "temp", .command = "", .status = .Pending, .retries =
    0, .dependencies = std.ArrayList(u32).init(allocator), .timeout_sec = 0 }, action_hash);
    if (cache_result == CacheResult.Hit) {
        // extract artifact from cache
        const cache_dir = try cacheDir(allocator, "temp");
        const artifact_src = try std.fs.path.join(allocator, &[_][]const u8{ cache_dir, "artifact" });
        try std.fs.copyFile(artifact_src, artifact_path);
        allocator.free(cache_dir);
        allocator.free(artifact_src);
        return true;
    }
    return false;
}

const std = @import("std");
const CacheResult = enum {
    Hit,
    Miss,
};

pub fn computeDependenciesHash(
    allocator: std.mem.Allocator,
    dependencies: [][]const u8,
) ![]const u8 {
    var hasher = std.crypto.hash.SHA256.init();
    for (dependencies) |dep| {
        const file_data = try std.fs.cwd().readFileAlloc(allocator, dep, 1024 * 1024);
        hasher.update(file_data);
        allocator.free(file_data);
    }
    const digest = hasher.final();
    var out = try allocator.alloc(u8, digest.len);
    std.mem.copy(u8, out, digest[0..]);
    return out;
}
pub fn storeCache(
    allocator: std.mem.Allocator,
    job: Job,
    hash: []const u8,
    artifact_path: []const u8,
) !void {
    const dir = try cacheDir(allocator, job.name);

    var cwd = std.fs.cwd();
    const cache = cwd.createDir(dir, .{}) catch |err| {
        if (err != std.fs.Error.DirAlreadyExists) return err;
    };

    defer cache.close();

    // store artifact
    const artifact_dest = try std.fs.path.join(allocator, &[_][]const u8{ dir, "artifact" });
    try std.fs.copyFile(artifact_path, artifact_dest);

    // store hash
    const hash_path = try std.fs.path.join(allocator, &[_][]const u8{ dir, "hash" });
    var hash_file = try cwd.createFile(hash_path, .{});
    defer hash_file.close();
    try hash_file.writeAll(hash);

    allocator.free(artifact_dest);
    allocator.free(hash_path);
}
pub fn computeHash(
    allocator: std.mem.Allocator,
    dependencies: [][]const u8,
) ![]const u8 {
    var hasher = std.crypto.hash.SHA256.init();
    for (dependencies) |dep| {
        const file_data = try std.fs.cwd().readFileAlloc(allocator, dep, 1024 * 1024);
        hasher.update(file_data);
        allocator.free(file_data);
    }
    const digest = hasher.final();
    var out = try allocator.alloc(u8, digest.len);
    std.mem.copy(u8, out, digest[0..]);
    return out;
}
