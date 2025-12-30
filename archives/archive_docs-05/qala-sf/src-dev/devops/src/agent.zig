const std = @import("std");

pub const Agent = struct {
    allocator: *std.mem.Allocator,
    controller_url: []const u8,
    labels: []const u8,

    pub fn init(allocator: *std.mem.Allocator, config_path: []const u8) !Agent {
        var file = try std.fs.cwd().openFile(config_path, .{});
        defer file.close();
        var json = try file.readToEndAlloc(allocator, 10_000);

        const parsed = try std.json.parseFromSlice(std.json.Value, allocator, json, .{});

        return .{
            .allocator = allocator,
            .controller_url = parsed.object.get("controller").?.string,
            .labels = parsed.object.get("labels").?.string,
        };
    }

    pub fn start(self: *Agent) !void {
        var ws = try std.net.tcpConnectToHost(self.allocator, self.controller_url, 9091);
        defer ws.close();

        std.debug.print("Connected to controller: {s}\n", .{self.controller_url});

        var buf: [2000]u8 = undefined;

        while (true) {
            const n = ws.reader().read(&buf) catch break;
            if (n == 0) continue;

            const msg = buf[0..n];

            if (std.mem.containsAtLeast(u8, msg, 1, "run")) {
                async self.runJob(&ws, msg);
            }
        }
    }

    fn runJob(self: *Agent, ws: *std.net.Stream, msg: []const u8) void {
        // parse command
        // execute locally like before
        // stream logs chunk by chunk:
        ws.writer().print(
            "{{\"type\":\"log\",\"job_id\":{},\"chunk\":\"{s}\"}}\n",
            .{ 1, "starting..." },
        ) catch {};
    }
};



const AgentConn = struct {
    id: u32,
    stream: *std.net.Stream,
    labels: []const u8,
    last_heartbeat: u64,
    running_jobs: usize,
};

// Jobs are assigned like:
fn pickAgent(self: *Controller, job: *Job) ?*AgentConn {
    var best: ?*AgentConn = null;

    for (self.agents.items) |*agent| {
        if (agent.running_jobs < self.max_jobs_per_agent) {
            if (best == null or agent.running_jobs < best.?.running_jobs) {
                best = agent;
            }
        }
    }
    return best;
}
    // send job to agent
    ws.writer().print(
        "{{\"type\":\"run\",\"job_id\":{},\"script\":\"{s}\"}}\n",
        .{ job.id, job.script },
    ) catch {};
pub fn copyFromCache(
    allocator: std.mem.Allocator,
    action_hash: []const u8,
    dest_path: []const u8,
) !void {
    const path = try std.fmt.allocPrint(allocator, "cache/{s}/attestation.json", .{action_hash});
    var file = std.fs.cwd().openFile(path, .{});
    defer file.close();
    try file.copyToPath(dest_path);
}
//     return file.readToEndAlloc(allocator, 10_000);
// }
//     return att;
// }

pub fn storeToCache(
    allocator: std.mem.Allocator,
    action_hash: []const u8,
    att: []const u8,
) !void {
    try std.fs.cwd().makePath("cache/{s}", .{action_hash});
    const dest_path = try std.fmt.allocPrint(allocator, "cache/{s}/attestation.json", .{action_hash});
    var file = try std.fs.cwd().createFile(dest_path, .{});
    defer file.close();
    try file.writeAll(att);
}
