// @license("MIT")
// @brief("")
// @author("qala development team")
// @copyright("2024 qala development team")
const std = @import("std");
const Job = @import("build.zig").Job;
const PipelineJob = @import("pipeline.zig").PipelineJob;

pub fn parseConfig(allocator: std.mem.Allocator, text: []const u8) ![]PipelineJob {
    var list = std.ArrayList(PipelineJob).init(allocator);

    var iter = std.mem.tokenize(u8, text, "\n");
    var current: ?PipelineJob = null;

    while (iter.next()) |line| {
        const trimmed = std.mem.trim(u8, line, " \t");

        if (trimmed.len == 0 or trimmed[0] == '#') continue;

        if (trimmed[0] != ' ') {
            // New job
            if (current) |c| try list.append(c);
            current = PipelineJob{
                .job = Job{ .name = trimmed, .command = "" },
                .deps = &[_][]const u8{},
            };
        } else if (std.mem.startsWith(u8, trimmed, "cmd:")) {
            current.?.job.command = trimmed[4..].trim(" ");
        } else if (std.mem.startsWith(u8, trimmed, "deps:")) {
            const rest = trimmed[5..].trim(" ");
            var deps_iter = std.mem.tokenize(u8, rest, ",");
            var deps_list = std.ArrayList([]const u8).init(allocator);

            while (deps_iter.next()) |d| {
                try deps_list.append(std.mem.trim(u8, d, " "));
            }
            current.?.deps = deps_list.toOwnedSlice();
        }
    }
    if (current) |c| try list.append(c);

    return list.toOwnedSlice();
}

const std = @import("std");

pub const Step = struct {
    command: []const u8,
};

pub const Job = struct {
    name: []const u8,
    steps: []Step,
};

pub const Pipeline = struct {
    jobs: []Job,
};

pub const Config = struct {
    pipeline: Pipeline,

    pub fn parse(allocator: std.mem.Allocator, text: []const u8) !Config {
        var jobs = std.ArrayList(Job).init(allocator);

        var it = std.mem.tokenizeScalar(text, '\n');
        var current_job: ?Job = null;

        while (it.next()) |line_raw| {
            const line = std.mem.trim(u8, line_raw, " \t");

            if (std.mem.startsWith(u8, line, "job")) {
                const name_start = std.mem.indexOfScalar(u8, line, '"') orelse unreachable;
                const name_end = std.mem.lastIndexOfScalar(u8, line, '"') orelse unreachable;
                const name = line[name_start + 1 .. name_end];

                current_job = Job{
                    .name = name,
                    .steps = &[_]Step{},
                };
            } else if (std.mem.startsWith(u8, line, "needs")) {
                // format: needs = ["a", "b"]
                const list_start = std.mem.indexOfScalar(u8, line, '[') orelse continue;
                const list_end = std.mem.indexOfScalar(u8, line, ']') orelse continue;
                const list_raw = line[list_start + 1 .. list_end];

                var split = std.mem.tokenizeScalar(list_raw, ',');
                var names = std.ArrayList([]const u8).init(allocator);

                while (split.next()) |item_raw| {
                    var item = std.mem.trim(u8, item_raw, " \t\"");
                    if (item.len > 0) try names.append(item);
                }

                var job = current_job.?;
                job.needs = try names.toOwnedSlice();
                current_job = job;
            } else if (std.mem.startsWith(u8, line, "\"")) {
                const end = std.mem.indexOfScalarPos(u8, line, 1, '"') orelse unreachable;
                const cmd = line[1..end];

                var job = current_job.?;
                const new_step = Step{ .command = cmd };

                const old_len = job.steps.len;
                var new_steps = try allocator.alloc(Step, old_len + 1);
                std.mem.copy(Step, new_steps, job.steps);
                new_steps[old_len] = new_step;

                job.steps = new_steps;
                current_job = job;
            } else if (std.mem.startsWith(u8, line, "}")) {
                if (current_job) |job| {
                    try jobs.append(job);
                    current_job = null;
                }
            }
        }

        return Config{
            .pipeline = Pipeline{
                .jobs = try jobs.toOwnedSlice(),
            },
        };
    }
};
