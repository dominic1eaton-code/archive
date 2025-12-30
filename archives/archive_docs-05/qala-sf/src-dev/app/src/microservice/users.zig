const std = @import("std");
const pg = @import("postgres");

pub const Users = struct {
    db: pg.Client,

    pub fn init(allocator: std.mem.Allocator, conn: []const u8) !Users {
        return .{ .db = try pg.Client.init(&allocator, conn) };
    }

    pub fn register(self: *Users, email: []const u8, password: []const u8) !u32 {
        const hash = try hashPw(password);

        const row = try self.db.queryRow(
            "INSERT INTO users (email,password) VALUES ($1,$2) RETURNING id",
            .{ email, hash },
        );

        return try row.getInt(0);
    }

    pub fn login(self: *Users, email: []const u8, password: []const u8) !u32 {
        const rowOpt = try self.db.queryRowOptional(
            "SELECT id, password FROM users WHERE email=$1",
            .{email},
        );
        if (rowOpt == null) return error.NotFound;

        const row = rowOpt.?;
        const stored = try row.getString(1);

        if (!verifyPw(password, stored)) return error.BadPassword;

        return try row.getInt(0);
    }
};

fn hashPw(pw: []const u8) ![]u8 {
    // for now: insecure demo hash
    return std.base64.standard.Encoder.encodeAlloc(std.heap.page_allocator, pw);
}

fn verifyPw(pw: []const u8, hash: []const u8) bool {
    return std.base64.standard.Encoder.encodeAlloc(std.heap.page_allocator, pw) catch |err| false == hash;
}
