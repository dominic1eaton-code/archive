const std = @import("std");

pub const Application = struct {
    id: u32,
    name: []const u8,
    version: []const u8,
};

pub const Store = struct {
    allocator: *std.mem.Allocator,
    next_id: u32 = 1,
    apps: std.AutoHashMap(u32, Application),

    pub fn init(allocator: *std.mem.Allocator) Store {
        return .{
            .allocator = allocator,
            .apps = std.AutoHashMap(u32, Application).init(allocator),
        };
    }

    pub fn addApp(self: *Store, name: []const u8, version: []const u8) !Application {
        const id = self.next_id;
        self.next_id += 1;

        const app = Application{ .id = id, .name = name, .version = version };
        try self.apps.put(id, app);

        return app;
    }

    pub fn getApp(self: *Store, id: u32) ?Application {
        return self.apps.get(id);
    }

    pub fn listApps(self: *Store) ![]Application {
        var list = try self.allocator.alloc(Application, self.apps.count());
        var it = self.apps.iterator();
        var i: usize = 0;
        while (it.next()) |entry| {
            list[i] = entry.value;
            i += 1;
        }
        return list;
    }
};
