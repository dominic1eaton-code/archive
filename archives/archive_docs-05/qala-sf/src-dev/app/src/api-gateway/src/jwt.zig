const std = @import("std");

pub const Jwt = struct {
    secret: []const u8,

    pub fn init(secret: []const u8) Jwt {
        return .{ .secret = secret };
    }

    pub fn sign(self: *Jwt, user_id: u32, allocator: std.mem.Allocator) ![]u8 {
        var claims = std.json.Value{ .Object = .{ .entries = &[_]std.json.Object.Entry{
            .{ .name = "sub", .value = .{ .String = try std.fmt.allocPrint(allocator, "{}", .{user_id}) } },
            .{ .name = "exp", .value = .{ .Integer = @intCast(i64, std.time.timestamp() + 3600) } },
        } } };

        return try std.crypto.jwt.encodeHS256(allocator, claims, self.secret);
    }

    pub fn verify(self: *Jwt, token: []const u8, allocator: std.mem.Allocator) !u32 {
        const claims = try std.crypto.jwt.decodeHS256(allocator, token, self.secret);

        if (!claims.object.contains("sub")) return error.InvalidToken;

        const uid_str = claims.object.get("sub").?.string;
        return try std.fmt.parseInt(u32, uid_str, 10);
    }
};
