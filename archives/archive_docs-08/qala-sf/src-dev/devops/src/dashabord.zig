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
    dependencies: std.ArrayList(u32>,
    timeout_sec: u64,
    log_file: []const u8,
    log_data: std.ArrayList(u8>,
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

    fn canRun(self: *Pipeline, job: *Job) bool {
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
            defer child.deinit();

            try child.setArgv(&.{ job.command });
            const stdout_pipe = try child.stdoutReader();
            const stderr_pipe = try child.stderrReader();
            try child.spawn();

            var buf: [1024]u8 = undefined;
            const start_time = std.time.milliTimestamp();
            var finished: bool = false;

            while (!finished) {
                const elapsed = std.time.milliTimestamp() - start_time;
                if (elapsed / 1000 > job.timeout_sec) {
                    try child.kill();
                    job.status = .Timeout;
                    _ = try self.updateLog(job, "Job timed out\n");
                    return;
                }

                const r = try stdout_pipe.read(&buf);
                if (r > 0) try self.updateLog(job, buf[0..r]);

                const e = try stderr_pipe.read(&buf);
                if (e > 0) try self.updateLog(job, buf[0..e]);

                if (!child.isRunning()) finished = true;
            }

            const result = try child.wait();
            if (result == 0) {
                job.status = .Success;
                _ = try self.updateLog(job, "Job succeeded\n");
                return;
            } else if (attempt <= job.retries) {
                _ = try self.updateLog(job, "Retrying job...\n");
            } else {
                job.status = .Failure;
                _ = try self.updateLog(job, "Job failed\n");
            }
        }
    }

    pub fn runPipeline(self: *Pipeline) !void {
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

    pub fn serveWebDashboard(self: *Pipeline, port: u16) !void {
        var listener = try std.net.StreamServer.listen(std.heap.page_allocator, "0.0.0.0", port);
        defer listener.deinit();

        while (true) {
            const conn = try listener.accept();
            async {
                var stdout = conn.writer();
                const html = \\<!DOCTYPE html>
                <html>
                <head>
                    <title>Mini-CD Dashboard</title>
                    <style>body { font-family: sans-serif; }</style>
                </head>
                <body>
                    <h1>Pipeline Dashboard</h1>
                    <ul id="jobs"></ul>
                    <script>
                        const evtSource = new EventSource("/events");
                        evtSource.onmessage = function(event) {
                            const data = JSON.parse(event.data);
                            const jobsEl = document.getElementById("jobs");
                            jobsEl.innerHTML = "";
                            for (let job of data) {
                                const li = document.createElement("li");
                                li.textContent = `${job.name}: ${job.status}`;
                                jobsEl.appendChild(li);
                            }
                        };
                    </script>
                </body>
                </html>
                \\;

                try stdout.print(
                    "HTTP/1.1 200 OK\r\nContent-Type: text/html\r\nContent-Length: {d}\r\n\r\n{s}",
                    .{ html.len, html }
                );
            }();
        }
    }

    pub fn serveEvents(self: *Pipeline, port: u16) !void {
        var listener = try std.net.StreamServer.listen(std.heap.page_allocator, "0.0.0.0", port);
        defer listener.deinit();

        while (true) {
            const conn = try listener.accept();
            async {
                var stdout = conn.writer();
                try stdout.print("HTTP/1.1 200 OK\r\nContent-Type: text/event-stream\r\nCache-Control: no-cache\r\n\r\n", .{});

                while (true) {
                    // Send job status JSON every second
                    var sb = std.ArrayList(u8).init(std.heap.page_allocator);
                    try sb.appendSlice("[");
                    for (self.jobs.items) |job, i| {
                        if (i > 0) try sb.appendSlice(",");
                        try sb.appendSlice("{\"name\":\"");
                        try sb.appendSlice(job.name);
                        try sb.appendSlice("\",\"status\":\"");
                        try sb.appendSlice(switch (job.status) {
                            .Pending => "Pending",
                            .Running => "Running",
                            .Success => "Success",
                            .Failure => "Failure",
                            .Timeout => "Timeout",
                        });
                        try sb.appendSlice("\"}");
                    }
                    try sb.appendSlice("]");

                    try stdout.print("data: {s}\n\n", .{sb.toSlice()});
                    std.time.sleep(1_000_000_000); // 1s
                    sb.deinit();
                }
            }();
        }
    }
};

pub fn main() !void {
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    const allocator = &gpa.allocator;

    var pipeline = Pipeline.init(allocator, 2);

    // Example hard-coded jobs
    try pipeline.jobs.append(Job{
        .id = 1, .name = "Build", .command = "echo Build && sleep 2", .status = .Pending,
        .retries = 1, .dependencies = std.ArrayList(u32).init(allocator), .timeout_sec = 5,
        .log_file = "build.log", .log_data = std.ArrayList(u8).init(allocator)
    });

    try pipeline.jobs.append(Job{
        .id = 2, .name = "Test", .command = "echo Test && sleep 3", .status = .Pending,
        .retries = 1, .dependencies = std.ArrayList(u32).init(allocator), .timeout_sec = 5,
        .log_file = "test.log", .log_data = std.ArrayList(u8).init(allocator)
    });

    // Start pipeline and dashboard concurrently
    async {
        try pipeline.runPipeline();
    }();
    async {
        try pipeline.serveWebDashboard(8080);
    }();
    async {
        try pipeline.serveEvents(8081);
    }();
}

