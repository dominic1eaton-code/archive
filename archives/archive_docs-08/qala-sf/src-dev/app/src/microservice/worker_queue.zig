const std = @import("std");

pub const WorkerQueue = struct {
    allocator: *std.mem.Allocator,
    pool: std.ThreadPool,
    task_fn: ?fn(data: []const u8) void,

    pub fn init(allocator: *std.mem.Allocator, concurrency: u32, task_fn: fn(data: []const u8) void) !WorkerQueue {
        var pool = try std.ThreadPool.init(concurrency, 4096, .{});
        return .{
            .allocator = allocator,
            .pool = pool,
            .task_fn = task_fn,
        };
    }

    pub fn enqueue(self: *WorkerQueue, data: []const u8) void {
        _ = self.pool.spawn(.{}, taskRunner, &WorkerTask{ .fn = self.task_fn, .data = data });
    }
};

const WorkerTask = struct {
    fn: ?fn([]const u8) void,
    data: []const u8,
};

fn taskRunner(task: *WorkerTask) void {
    if (task.fn) |f| f(task.data);
}
