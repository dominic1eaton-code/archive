// @license("MIT")
// @brief("")
// @author("qala development team")
const std = @import("std");

const JobStatus = enum {
    Pending,
    Running,
    Success,
    Failure,
};

const Job = struct {
    id: u32,
    name: []const u8,
    status: JobStatus,
};

const Pipeline = struct {
    jobs: std.ArrayList(Job),
    allocator: *std.mem.Allocator,

    pub fn init(allocator: *std.mem.Allocator) Pipeline {
        return Pipeline{
            .jobs = std.ArrayList(Job).init(allocator),
            .allocator = allocator,
        };
    }

    pub fn addJob(self: *Pipeline, id: u32, name: []const u8) !void {
        const job = Job{
            .id = id,
            .name = name,
            .status = .Pending,
        };
        try self.jobs.append(job);
    }

    pub fn run(self: *Pipeline) void {
        var stdout = std.io.getStdOut().writer();
        for (self.jobs.items) |*job| {
            job.status = .Running;
            _ = stdout.print("Running job: {s}\n", .{job.name});

            // Simulate job execution
            if (job.id % 2 == 0) {
                job.status = .Success;
                _ = stdout.print("Job {s} succeeded\n", .{job.name});
            } else {
                job.status = .Failure;
                _ = stdout.print("Job {s} failed\n", .{job.name});
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
                },
            });
        }
    }
};

pub fn main() !void {
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    const allocator = &gpa.allocator;

    var pipeline = Pipeline.init(allocator);
    try pipeline.addJob(1, "Build");
    try pipeline.addJob(2, "Test");
    try pipeline.addJob(3, "Deploy");

    pipeline.run();
    pipeline.report();
}

//////////////////
/// 

const std = @import("std");

const JobStatus = enum {
    Pending,
    Running,
    Success,
    Failure,
};

const Job = struct {
    id: u32,
    name: []const u8,
    command: []const u8,
    status: JobStatus,
};

const Pipeline = struct {
    jobs: std.ArrayList(Job>,
    allocator: *std.mem.Allocator,

    pub fn init(allocator: *std.mem.Allocator) Pipeline {
        return Pipeline{
            .jobs = std.ArrayList(Job).init(allocator),
            .allocator = allocator,
        };
    }

    pub fn addJob(self: *Pipeline, id: u32, name: []const u8, command: []const u8) !void {
        const job = Job{
            .id = id,
            .name = name,
            .command = command,
            .status = .Pending,
        };
        try self.jobs.append(job);
    }

    pub fn runAsync(self: *Pipeline) !void {
        var stdout = std.io.getStdOut().writer();
        var gpa = std.heap.GeneralPurposeAllocator(.{}){};
        const allocator = &gpa.allocator;

        var tasks = std.ArrayList(async void).init(allocator);

        for (self.jobs.items) |*job| {
            try tasks.append(async {
                job.status = .Running;
                _ = stdout.print("Starting job: {s}\n", .{job.name});

                var child = try std.ChildProcess.init(allocator);
                defer child.deinit();

                try child.setArgv(&.{ job.command });
                try child.spawn();

                const result = try child.wait();

                if (result == 0) {
                    job.status = .Success;
                    _ = stdout.print("Job {s} succeeded\n", .{job.name});
                } else {
                    job.status = .Failure;
                    _ = stdout.print("Job {s} failed\n", .{job.name});
                }
            }());
        }

        // Wait for all async tasks to finish
        for (tasks.items) |task| {
            _ = task.await;
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
                },
            });
        }
    }
};

pub fn main() !void {
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    const allocator = &gpa.allocator;

    var pipeline = Pipeline.init(allocator);
    try pipeline.addJob(1, "Build", "echo Building project");
    try pipeline.addJob(2, "Test", "echo Running tests");
    try pipeline.addJob(3, "Deploy", "echo Deploying application");

    try pipeline.runAsync();
    pipeline.report();
}
///////////////////
/// Caching utilities for CI/CD jobs
/// @license("MIT")
const std = @import("std");
const Job = @import("job.zig").Job;
pub const CacheResult = enum {
    Hit,
    Miss,
};
pub fn computeJobHash(
    allocator: std.mem.Allocator,
    job: Job,
    dependencies: []const []const u8, // paths or hashes from dependent jobs
) ![]u8 {
    var hasher = std.crypto.hash.sha256.Sha256.init(.{});

    // hash job name
    hasher.update(job.name);

    // hash command
    hasher.update(job.command);

    // hash dependency outputs
    for (dependencies) |dep| {
        hasher.update(dep);
    }

    const digest = hasher.finalResult();
    var out = try allocator.alloc(u8, digest.len);
    std.mem.copy(u8, out, digest[0..]);
    return out;
}
pub fn cacheDir(allocator: std.mem.Allocator, job_name: []const u8) ![]const u8 {
    return try std.fs.path.join(allocator, &[_][]const u8{
        ".ci_cache", "jobs", job_name,
    });
}
pub fn checkCache(
    allocator: std.mem.Allocator,
    job: Job,
    hash: []const u8,
) !CacheResult {
    const dir = try cacheDir(allocator, job.name);
    var cwd = std.fs.cwd();
    var cache = cwd.openDir(dir, .{}) catch return CacheResult.Miss;
    defer cache.close();
    // read hash file
    const hash_path = "hash";
    const stored = cache.readFileAlloc(allocator, hash_path, 1024) catch return CacheResult.Miss;
    if (std.mem.eql(u8, stored, hash))
        return CacheResult.Hit;
    return CacheResult.Miss;
}


const std = @import("std");

const JobStatus = enum {
    Pending,
    Running,
    Success,
    Failure,
};

const Job = struct {
    id: u32,
    name: []const u8,
    command: []const u8,
    status: JobStatus,
    retries: u8,
    dependencies: std.ArrayList(u32),
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

    pub fn addJob(self: *Pipeline, id: u32, name: []const u8, command: []const u8, retries: u8, deps: []const u32) !void {
        var dep_list = std.ArrayList(u32).init(self.allocator);
        for (deps) |dep| try dep_list.append(dep);

        const job = Job{
            .id = id,
            .name = name,
            .command = command,
            .status = .Pending,
            .retries = retries,
            .dependencies = dep_list,
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

    pub fn run(self: *Pipeline) !void {
        var stdout = std.io.getStdOut().writer();
        var gpa = std.heap.GeneralPurposeAllocator(.{}){};
        const allocator = &gpa.allocator;

        var active_jobs: std.ArrayList(async void) = std.ArrayList(async void).init(allocator);

        while (true) {
            var progress = false;

            // Launch eligible jobs
            for (self.jobs.items) |*job| {
                if (job.status == .Pending and self.canRun(job) and active_jobs.items.len < self.max_concurrent) {
                    progress = true;

                    job.status = .Running;
                    _ = stdout.print("Starting job: {s}\n", .{job.name});

                    try active_jobs.append(async {
                        var attempt: u8 = 0;
                        var result: i32 = 1;
                        while (attempt <= job.retries and result != 0) : (attempt += 1) {
                            var child = try std.ChildProcess.init(allocator);
                            defer child.deinit();

                            try child.setArgv(&.{ job.command });
                            try child.spawn();
                            result = try child.wait();

                            if (result != 0 and attempt < job.retries) {
                                _ = stdout.print("Job {s} failed, retry {d}\n", .{job.name, attempt});
                            }
                        }

                        if (result == 0) {
                            job.status = .Success;
                            _ = stdout.print("Job {s} succeeded\n", .{job.name});
                        } else {
                            job.status = .Failure;
                            _ = stdout.print("Job {s} failed after {d} retries\n", .{job.name, job.retries});
                        }
                    }());
                }
            }

            // Await any active job if we have reached the parallel limit
            if (active_jobs.items.len >= self.max_concurrent or not progress) {
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

    try pipeline.addJob(1, "Build", "echo Building project", 1, &.{});
    try pipeline.addJob(2, "Test", "echo Running tests", 2, &.{1}); // Depends on Build
    try pipeline.addJob(3, "Deploy", "echo Deploying application", 1, &.{2}); // Depends on Test
    try pipeline.addJob(4, "Lint", "echo Linting code", 0, &.{1}); // Depends on Build

    try pipeline.run();
    pipeline.report();
}


pub fn storeCache(
    allocator: std.mem.Allocator,
    job: Job,
    hash: []const u8,
    artifact_path: []const u8,
) !void {
    var cwd = std.fs.cwd();

    const dir = try cacheDir(allocator, job.name);
    try cwd.makePath(dir);

    var cache = cwd.openDir(dir, .{ .create = true }) ;
    defer cache.close();

    // write hash file
    const hash_path = "hash";
    try cache.writeFile(hash_path, hash);

    // copy artifact
    const artifact_dest = try std.fs.path.join(allocator, &[_][]const u8{ dir, "artifact" });
    defer allocator.free(artifact_dest);

    try std.fs.copyFile(artifact_path, artifact_dest);
}
pub fn tryLoadFromCache(
    allocator: std.mem.Allocator,
    action_hash: []const u8,
    job: Job,
) !?[]const u8 {
    const dir = try cacheDir(allocator, job.name);
    var cwd = std.fs.cwd();
    var cache = cwd.openDir(dir, .{}) catch return null;
    defer cache.close();

    // read hash file
    const hash_path = "hash";
    const stored = cache.readFileAlloc(allocator, hash_path, 1024) catch return null;

    if (!std.mem.eql(u8, stored, action_hash))
        return null;

    // load artifact
    const artifact_path = try std.fs.path.join(allocator, &[_][]const u8{ dir, "artifact" });
    defer allocator.free(artifact_path);

    const artifact = cache.readFileAlloc(allocator, artifact_path, 10 * 1024 * 1024) catch return null;

    return artifact;
}

pub fn tryLoadFromCache(
    allocator: std.mem.Allocator,
    action_hash: []const u8,
) !?[]u8 {
    const path = try std.fmt.allocPrint(allocator, "cache/{s}/attestation.json", .{action_hash});
    var file = std.fs.cwd().openFile(path, .{}) catch return null;
    defer file.close();
    const data = file.readToEndAlloc(allocator, 10 * 1024 * 1024) catch return null;
    return data;
}

pub fn computeJobHash(
    allocator: std.mem.Allocator,
    job: Job,
    dependencies: []const []const u8, // paths or hashes from dependent jobs
) ![]u8 {
    var hasher = std.crypto.hash.sha256.Sha256.init(.{});

    // hash job name
    hasher.update(job.name);

    // hash command
    hasher.update(job.command);

    // hash dependency outputs
    for (dependencies) |dep| {
        hasher.update(dep);
    }

    const digest = hasher.finalResult();
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
    var cwd = std.fs.cwd();
    const dir = try cacheDir(allocator, job.name);
    try cwd.makePath(dir);

    var cache = cwd.openDir(dir, .{ .create = true }) ;
    defer cache.close();

    // write hash file
    const hash_path = "hash";
    try cache.writeFile(hash_path, hash);

    // copy artifact
    const artifact_dest = try std.fs.path.join(allocator, &[_][]const u8{ dir, "artifact" });
    defer allocator.free(artifact_dest);

    try std.fs.copyFile(artifact_path, artifact_dest);
}
