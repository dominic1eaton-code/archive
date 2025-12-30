const std = @import("std");
const sqlite = @import("sqlite");

pub const ArtifactMeta = struct {
    id: i64,
    name: []const u8,
    version: []const u8,
    hash: []const u8,
    path: []const u8,
    created_at: u64,
};

pub const Db = struct {
    inner: sqlite.Db,

    pub fn init(path: []const u8) !Db {
        var db = try sqlite.Db.init(.{
            .mode = .{ .File = path },
            .open_flags = .{ .write = true, .create = true },
            .threading_mode = .MultiThread,
        });
        try db.exec(
            \\CREATE TABLE IF NOT EXISTS artifacts (
              id INTEGER PRIMARY KEY,
              name TEXT,
              version TEXT,
              hash TEXT,
              path TEXT,
              created_at INTEGER
            )
            , .{}, .{});
        return Db{ .inner = db };
    }

    pub fn close(self: *Db) void {
        _ = self.inner.deinit();
    }

    pub fn insert(self: *Db, name: []const u8, version: []const u8, hash: []const u8, path: []const u8, ts: u64) !void {
        var stmt = try self.inner.prepare(
            \\INSERT INTO artifacts (name, version, hash, path, created_at) VALUES (?{[]const u8}, ?{[]const u8}, ?{[]const u8}, ?{[]const u8}, ?{u64})
        );
        defer stmt.deinit();
        try stmt.exec(.{}, .{
            .name = name,
            .version = version,
            .hash = hash,
            .path = path,
            .created_at = ts,
        });
    }

    pub fn get(self: *Db, name: []const u8, version: []const u8) !?ArtifactMeta {
        var stmt = try self.inner.prepare(
            \\SELECT id, name, version, hash, path, created_at FROM artifacts WHERE name = ?{[]const u8} AND version = ?{[]const u8} LIMIT 1
        );
        defer stmt.deinit();
        const row = try stmt.one(ArtifactMeta, .{}, .{ .name = name, .version = version });
        return row;
    }

    pub fn listByName(self: *Db, name: []const u8, allocator: std.mem.Allocator) ![]ArtifactMeta {
        var stmt = try self.inner.prepare(
            \\SELECT id, name, version, hash, path, created_at FROM artifacts WHERE name = ?{[]const u8}
        );
        defer stmt.deinit();
        return try stmt.all(ArtifactMeta, allocator, .{}, .{ .name = name });
    }
};
