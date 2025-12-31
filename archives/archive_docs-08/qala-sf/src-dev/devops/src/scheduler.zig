// @license("MIT")
// @brief("")
// @author("qala development team")
// @copyright("2024 qala development team")
const std = @import("std");
const Job = @import("config.zig").Job;
const runJob = @import("executor.zig").runJob;

pub fn runDAG(jobs: []Job, allocator: std.mem.Allocator) !void {
    const stdout = std.io.getStdOut().writer();

    // Map: job.name → index
    var map = std.StringHashMap(usize).init(allocator);

    for (jobs, 0..) |job, i| {
        try map.put(job.name, i);
    }

    // Build indegree + adjacency
    var indegree = try allocator.alloc(usize, jobs.len);
    @memset(indegree, 0);

    var edges = try allocator.alloc(std.ArrayList(usize), jobs.len);
    for (edges) |*lst| lst.* = std.ArrayList(usize).init(allocator);

    for (jobs, 0..) |job, j| {
        for (job.needs) |dep| {
            const idx = map.get(dep) orelse return error.UnknownDependency;
            try edges[idx].append(j);
            indegree[j] += 1;
        }
    }

    // Ready queue: jobs with indegree 0
    var ready = std.ArrayList(usize).init(allocator);
    for (indegree, 0..) |deg, i| {
        if (deg == 0) try ready.append(i);
    }

    if (ready.items.len == 0)
        return error.CyclicDependency;

    // Track completed jobs
    var complete = try allocator.alloc(bool, jobs.len);
    @memset(complete, false);

    try stdout.print("DAG scheduler starting...\n", .{});

    // Main loop
    while (true) {
        if (ready.items.len == 0) {
            // All done?
            var all = true;
            for (complete) |c| if (!c) all = false;

            if (all) break;
            return error.CyclicDependency;
        }

        // Spawn all ready jobs in parallel
        var threads = std.ArrayList(std.Thread).init(allocator);

// Spawn ready jobs
        var threads = std.ArrayList(std.Thread).init(allocator);

        for (ready.items) |idx| {
            const job = jobs[idx];

            // Paths
            const artifact_path = try std.fs.path.join(allocator, &[_][]const u8{
                ".ci_cache", "tmp", job.name ++ ".tar"
            });

            // collect dependent hashes
            var dep_hashes = std.ArrayList([]const u8).init(allocator);
            for (job.needs) |dep_name| {
                const dep_idx = map.get(dep_name) orelse unreachable;
                const dep_hash_path = try std.fs.path.join(
                    allocator,
                    &[_][]const u8{ ".ci_cache", "jobs", dep_name, "hash" },
                );
                const h = try std.fs.cwd().readFileAlloc(
                    allocator,
                    dep_hash_path,
                    1024,
                );
                try dep_hashes.append(h);
            }

            const job_hash = try cache.computeJobHash(
                allocator,
                job,
                dep_hashes.toOwnedSlice(),
            );

            // Check cache hit
            const result = try cache.checkCache(allocator, job, job_hash);

            if (result == .Hit) {
                std.debug.print("✓ Cache hit for job {s}\n", .{job.name});
                complete[idx] = true;
                continue;
            }

            std.debug.print("⟳ Cache miss for job {s}, executing...\n", .{job.name});

            const th = try std.Thread.spawn(.{}, runJobWithArtifacts, .{
                job, allocator, artifact_path,
            });

            try threads.append(th);

            // After completion, store cache
            // (we will do this AFTER thread join)
        }

        // Join threads and store their caches
        for (threads.items) |t| {
            t.join();
        }

        // After jobs ran, store caches
        for (ready.items) |idx| {
            if (!complete[idx]) {
                const job = jobs[idx];

                // recompute job hash (same inputs)
                const job_hash = ... same as above ...

                const artifact_path = try std.fs.path.join(allocator,
                    &[_][]const u8{ ".ci_cache", "tmp", job.name ++ ".tar" });

                try cache.storeCache(
                    allocator,
                    job,
                    job_hash,
                    artifact_path,
                );

                complete[idx] = true;
            }
        }

        // Clear ready after dispatch
        ready.clearRetainingCapacity();

        // Wait & mark complete
        for (threads.items, 0..) |t, k| {
            t.join();
            const idx = k; // mapping is 1:1 from ready before clearing
            complete[idx] = true;
        }

        // Update indegrees after completion
        for (jobs, 0..) |_, j| if (complete[j]) {
            for (edges[j].items) |neighbor| {
                if (indegree[neighbor] > 0) {
                    indegree[neighbor] -= 1;
                    if (indegree[neighbor] == 0 and !complete[neighbor]) {
                        try ready.append(neighbor);
                    }
                }
            }
        }
    }

    try stdout.print("DAG pipeline completed.\n", .{});
}

pub const error = error{
    UnknownDependency,
    CyclicDependency,
};
