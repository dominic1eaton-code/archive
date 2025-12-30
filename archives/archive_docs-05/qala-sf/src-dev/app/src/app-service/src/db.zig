const std = @import("std");
const pg = @import("rpostgresql");

pub const Db = struct {
    client: pg.Client,

    pub fn init(allocator: *std.mem.Allocator, conn_str: []const u8) !Db {
        var client = try pg.Client.init(allocator, conn_str);
        return .{ .client = client };
    }

    pub fn createApplication(self: *Db, name: []const u8, version: []const u8) !u32 {
        const row = try self.client.queryRow(
            "INSERT INTO applications(name, version) VALUES ($1, $2) RETURNING id;",
            .{ name, version },
        );

        return try row.getInt(0);
    }

    pub fn getApplication(self: *Db, id: u32) !?pg.Row {
        return try self.client.queryRowOptional(
            "SELECT id, name, version FROM applications WHERE id=$1;",
            .{id},
        );
    }

    pub fn listApplications(self: *Db) !pg.Rows {
        return try self.client.query(
            "SELECT id, name, version FROM applications;",
            .{},
        );
    }
};
