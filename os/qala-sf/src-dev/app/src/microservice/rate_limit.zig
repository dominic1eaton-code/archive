const std = @import("std");

pub const RateLimiter = struct {
    map: std.AutoHashMap([]const u8, Entry),
    limit: u32, // per minute

    pub const Entry = struct {
        tokens: u32,
        last_refill: i64,
    };

    pub fn init(allocator: *std.mem.Allocator, limit: u32) RateLimiter {
        return .{
            .map = std.AutoHashMap([]const u8, Entry).init(allocator),
            .limit = limit,
        };
    }

    pub fn allow(self: *RateLimiter, ip: []const u8) bool {
        const now = std.time.timestamp();

        var e = self.map.get(ip) orelse Entry{ .tokens = self.limit, .last_refill = now };
        if (now - e.last_refill >= 60) {
            e.tokens = self.limit;
            e.last_refill = now;
        }

        if (e.tokens == 0) {
            self.map.put(ip, e) catch {};
            return false;
        }

        e.tokens -= 1;
        self.map.put(ip, e) catch {};
        return true;
    }
};
