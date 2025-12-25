const std = @import("std");
const crypto = @import("std").crypto;

pub fn generateJWT(username: []const u8, role: []const u8, secret: []const u8, allocator: *std.mem.Allocator) ![]u8 {
    // Header {"alg":"HS256","typ":"JWT"}
    const header_json = "{ \"alg\": \"HS256\", \"typ\": \"JWT\" }";
    const payload_json = std.fmt.allocPrint(allocator, "{{\"sub\":\"{s}\",\"role\":\"{s}\",\"exp\":{d}}}", .{ username, role, std.time.milliTimestamp() + 3600_000 }) catch return error.OutOfMemory;

    const header_b64 = try base64urlEncode(allocator, header_json);
    const payload_b64 = try base64urlEncode(allocator, payload_json);

    const signing_input = std.fmt.allocPrint(allocator, "{s}.{s}", .{ header_b64, payload_b64 }) catch return error.OutOfMemory;

    var hmac = crypto.hmac.initSha256(secret);
    hmac.update(signing_input);
    const sig_bytes = hmac.final();

    const sig_b64 = try base64urlEncode(allocator, sig_bytes);

    const jwt = std.fmt.allocPrint(allocator, "{s}.{s}", .{ signing_input, sig_b64 }) catch return error.OutOfMemory;

    return jwt;
}

fn base64urlEncode(allocator: *std.mem.Allocator, input: []const u8) ![]u8 {
    var buf = try std.base64.encodeAlloc(allocator, input, .URL_SAFE);
    return buf;
}

pub fn verifyJWT(token: []const u8, secret: []const u8) !?Role {
    const parts = std.mem.split(u8, token, ".");

    if (parts.len != 3) return null;

    const signing_input = std.fmt.allocPrint(allocator, "{s}.{s}", .{ parts[0], parts[1] }) catch return null;

    var hmac = crypto.hmac.initSha256(secret);
    hmac.update(signing_input);
    const expected_sig = hmac.final();

    const actual_sig = try base64urlDecode(parts[2]);

    if (!std.mem.eql(u8, expected_sig, actual_sig)) return null;

    const payload_json = try base64urlDecode(parts[1]);
    const payload = try std.json.parseFromSlice(std.json.Value, allocator, payload_json, .{}) catch return null;

    const role_str = payload.object.get("role")?.string orelse return null;

    return RoleFromString(role_str);
}

fn base64urlDecode(input: []const u8) ![]u8 {
    var buf = try std.base64.decodeAlloc(allocator, input, .URL_SAFE);
    return buf;
}

enum Role {
    Admin,
    User,
}

fn RoleFromString(role_str: []const u8) ?Role {
    if (std.mem.eql(u8, role_str, "Admin")) {
        return Role.Admin;
    } else if (std.mem.eql(u8, role_str, "User")) {
        return Role.User;
    } else {
        return null;
    }
}

const JobStatus = enum {
    Pending,
    Running,
    Success,
    Failed,
    Timeout,
};

const Job = struct {
    id: u32,
    name: []const u8,
    command: []const u8,
    args: [][]const u8,
    status: JobStatus,
    retries: usize,
    dependencies: std.ArrayList(u32),
    timeout_sec: u64,
    log_file: []const u8,
    log_data: std.ArrayList(u8),
};

const Pipeline = struct {
    jobs: std.ArrayList(Job),
    allocator: *std.mem.Allocator,
    max_concurrent: usize,
    pub fn init(allocator: *std.mem.Allocator, max_concurrent: usize) Pipeline {
        return Pipeline{
            .jobs = std.ArrayList(Job).init(allocator),
            .allocator = allocator,
            .max_concurrent = max_concurrent,
        };
    }

    fn dependencies_met(self: *Pipeline, job: *Job) bool {
        for (job.dependencies.items) |dep_id| {
            for (self.jobs.items) |j| {
                if (j.id == dep_id and j.status != .Success) return false;
            }
        }
        return true;
    }

    fn updateLog(job: *Job, data: []const u8) !void {
        try job.log_data.appendSlice(data);
        // Append to log file
        var log_file = try std.fs.cwd().openFile(job.log_file, .{ .append = true }) catch |e| return e;
        defer log_file.close();
        try log_file.writeAll(data);
    }

    fn runJob(self: *Pipeline, job: *Job) async void {
        var allocator = self.allocator;
        job.status = .Running;
        _ = try self.updateLog(job, "Starting job\n");
        var attempt: u8 = 0;
        while (attempt <= job.retries) : (attempt += 1) {
            var child = try std.ChildProcess.init(allocator);
            try child.setExecutablePath(job.command);
            for (job.args) |arg| {
                try child.addArgument(arg);
            }
            const stdout_pipe = try child.stdoutReader();
            const stderr_pipe = try child.stderrReader();
            try child.spawn();
            defer child.deinit();
            var buf: [1024]u8 = undefined;
            const start_time = std.time.milliTimestamp();
            while (true) {
                const now = std.time.milliTimestamp();
                if (now - start_time > job.timeout_sec * 1000) {
                    try child.kill();
                    job.status = .Timeout;
                    _ = try self.updateLog(job, "Job timed out\n");
                    break;
                }

                const stdout_read = try stdout_pipe.read(&buf);
                if (stdout_read > 0) {
                    try self.updateLog(job, buf[0..stdout_read]);
                }

                const stderr_read = try stderr_pipe.read(&buf);
                if (stderr_read > 0) {
                    try self.updateLog(job, buf[0..stderr_read]);
                }

                if (child.isExited()) {
                    const exit_code = child.exitCode();
                    if (exit_code == 0) {
                        job.status = .Success;
                        _ = try self.updateLog(job, "Job completed successfully\n");
                    } else {
                        job.status = .Failed;
                        _ = try self.updateLog(job, "Job failed with exit code {d}\n", .{ exit_code });
                    }
                    break;
                }

                await std.time.sleep(100 * std.time.millisecond);
            }
        }

        if (job.status != .Success and attempt > job.retries) {
            job.status = .Failed;
            _ = try self.updateLog(job, "Job failed after {d} attempts\n", .{ attempt });
        }
    }

    fn runJob(self: *Pipeline, job: *Job) async void {
        var attempt: usize = 0;

        while (attempt <= job.retries) : (attempt += 1) {
            const child = try std.ChildProcess.init(self.allocator, job.command, job.args);
            const stdout_pipe = try child.stdoutReader();
            const stderr_pipe = try child.stderrReader();
            try child.spawn();
            defer child.deinit();
            var buf: [1024]u8 = undefined;
            const start_time = std.time.milliTimestamp();
            var finished: bool = false;
            job.status = .Running;
            _ = try self.updateLog(job, "Starting job attempt {d}\n", .{ attempt });
            while (!finished) {
                const now = std.time.milliTimestamp();
                if (now - start_time > job.timeout_sec * 1000) {
                    try child.kill();
                    job.status = .Timeout;
                    _ = try self.updateLog(job, "Job timed out\n");
                    break;
                }

                const stdout_read = try stdout_pipe.read(&buf);
                if (stdout_read > 0) {
                    try self.updateLog(job, buf[0..stdout_read]);
                }

                const stderr_read = try stderr_pipe.read(&buf);
                if (stderr_read > 0) {
                    try self.updateLog(job, buf[0..stderr_read]);
                }

                if (child.isExited()) {
                    const exit_code = child.exitCode();
                    if (exit_code == 0) {
                        job.status = .Success;
                        _ = try self.updateLog(job, "Job completed successfully\n");
                    } else {
                        job.status = .Failed;
                        _ = try self.updateLog(job, "Job failed with exit code {d}\n", .{ exit_code });
                    }
                    break;
                }

                await std.time.sleep(100 * std.time.millisecond);
            }
        }
        if (job.status != .Success and attempt > job.retries) {
            job.status = .Failed;
            _ = try self.updateLog(job, "Job failed after {d} attempts\n", .{ attempt });
        }
    }

    pub fn runPipeline(self: *Pipeline) !void {
        var active_jobs: std.ArrayList(async void> = std.ArrayList(async void).init(self.allocator);

        while (true) {
            var progress = false;

            for (self.jobs.items) |*job| {
                if (job.status == .Pending and job.dependencies_met()) {
                    progress = true;
                    active_jobs.append(self.runJob(job)) catch return error.OutOfMemory;
                }
            }

            if (!progress) break;

            var i: usize = 0;
            while (i < active_jobs.len) {
                const job_future = active_jobs.items[i];
                if (job_future.isComplete()) {
                    active_jobs.swapRemove(i);
                } else {
                    i += 1;
                }
            }

            await std.time.sleep(100 * std.time.millisecond);
        }

        for (self.jobs.items) |*job| {
            if (job.status != .Success) {
                return error.PipelineFailed;
            }
        }

        return;
    }

    fn runJob(self: *Pipeline, job: *Job) async void {
        var attempt: usize = 0;

        while (attempt <= job.retries) : (attempt += 1) {
            const child = try std.ChildProcess.init(self.allocator, job.command, job.args);
            const stdout_pipe = try child.stdoutReader();
            const stderr_pipe = try child.stderrReader();
            try child.spawn();
            defer child.deinit();
            var buf: [1024]u8 = undefined;
            const start_time = std.time.milliTimestamp();
            var finished: bool = false;
            job.status = .Running;
            _ = try self.updateLog(job, "Starting job attempt {d}\n", .{ attempt });
            while (!finished) {
                const now = std.time.milliTimestamp();
                if (now - start_time > job.timeout_sec * 1000) {
                    try child.kill();
                    job.status = .Timeout;
                    _ = try self.updateLog(job, "Job timed out\n");
                    break;
                }
                const stdout_read = try stdout_pipe.read(&buf);
                if (stdout_read > 0) {
                    try self.updateLog(job, buf[0..stdout_read]);
                }
                const stderr_read = try stderr_pipe.read(&buf);
                if (stderr_read > 0) {
                    try self.updateLog(job, buf[0..stderr_read]);
                }
                if (child.isExited()) {
                    const exit_code = child.exitCode();
                    if (exit_code == 0) {
                        job.status = .Success;
                        _ = try self.updateLog(job, "Job completed successfully\n");
                    } else {
                        job.status = .Failed;
                        _ = try self.updateLog(job, "Job failed with exit code {d}\n", .{ exit_code });
                    }
                    break;
                }
                await std.time.sleep(100 * std.time.millisecond);
            }
        }
        if (job.status != .Success and attempt > job.retries) {
            job.status = .Failed;
            _ = try self.updateLog(job, "Job failed after {d} attempts\n", .{ attempt });
        }
    }

    pub fn runPipeline(self: *Pipeline) !void {
        var active_jobs: std.ArrayList(async void> = std.ArrayList(async void).init(self.allocator);

        while (true) {
            var progress = false;

            for (self.jobs.items) |*job| {
                if (job.status == .Pending and job.dependencies_met()) {
                    progress = true;
                    active_jobs.append(self.runJob(job)) catch return error.OutOfMemory;
                }
            }

            if (!progress) break;

            var i: usize = 0;
            while (i < active_jobs.len) {
                const job_future = active_jobs.items[i];
                if (job_future.isComplete()) {
                    active_jobs.swapRemove(i);
                } else {
                    i += 1;
                }
            }

            await std.time.sleep(100 * std.time.millisecond);
        }

        for (self.jobs.items) |*job| {
            if (job.status != .Success) {
                return error.PipelineFailed;
            }
        }

        return;
    }

