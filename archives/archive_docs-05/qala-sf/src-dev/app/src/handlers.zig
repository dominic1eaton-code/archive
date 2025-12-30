const std = @import("std");
const Store = @import("store.zig").Store;

pub const Handlers = struct {
    store: *Store,

    pub fn listApps(self: *Handlers, res: *std.http.Server.Response) !void {
        const apps = try self.store.listApps();
        defer self.store.allocator.free(apps);

        var json = std.json.writeStream(res.writer());
        try json.beginArray();
        for (apps) |app| {
            try json.beginObject();
            try json.objectField("id");
            try json.write(app.id);
            try json.objectField("name");
            try json.write(app.name);
            try json.objectField("version");
            try json.write(app.version);
            try json.endObject();
        }
        try json.endArray();
    }

    pub fn createApp(self: *Handlers, req: *std.http.Server.Request, res: *std.http.Server.Response) !void {
        var arena = std.heap.ArenaAllocator.init(self.store.allocator);
        defer arena.deinit();

        var json_parser = std.json.Parser.init(&arena.allocator);
        const root = try json_parser.parseFromSlice(req.body);

        const name = root.object.get("name").?.string;
        const version = root.object.get("version").?.string;

        const app = try self.store.addApp(name, version);

        var json = std.json.writeStream(res.writer());
        try json.beginObject();
        try json.objectField("id");
        try json.write(app.id);
        try json.objectField("name");
        try json.write(app.name);
        try json.objectField("version");
        try json.write(app.version);
        try json.endObject();
    }
};

pub const error = struct {
    AppNotFound: error{},
};
