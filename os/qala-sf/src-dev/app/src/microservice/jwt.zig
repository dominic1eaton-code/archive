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

const std = @import("std");

pub const JwtPair = struct {
    access: []u8,
    refresh: []u8,
};

pub const Jwt = struct {
    secret: []const u8,

    pub fn init(secret: []const u8) Jwt {
        return .{ .secret = secret };
    }

    pub fn createTokens(self: *Jwt, user_id: u32, allocator: std.mem.Allocator) !JwtPair {
        const access = try self.sign(user_id, allocator, 3600); // 1 hour
        const refresh = try self.sign(user_id, allocator, 86400 * 30); // 30 days
        return .{ .access = access, .refresh = refresh };
    }

    pub fn sign(self: *Jwt, user_id: u32, allocator: std.mem.Allocator, ttl: i64) ![]u8 {
        const now = std.time.timestamp();
        const exp = now + ttl;

        var claims = std.json.Value{ .Object = .{ .entries = &[_]std.json.Object.Entry{
            .{ .name = "sub", .value = .{ .String = try std.fmt.allocPrint(allocator, "{}", .{user_id}) } },
            .{ .name = "exp", .value = .{ .Integer = exp } },
        } } };

        return try std.crypto.jwt.encodeHS256(allocator, claims, self.secret);
    }

    pub fn verify(self: *Jwt, token: []const u8, allocator: std.mem.Allocator) !u32 {
        const claims = try std.crypto.jwt.decodeHS256(allocator, token, self.secret);

        const exp = claims.object.get("exp") orelse return error.InvalidToken;
        if (try exp.integer < std.time.timestamp()) return error.Expired;

        const sub = claims.object.get("sub") orelse return error.InvalidToken;
        return try std.fmt.parseInt(u32, sub.string, 10);
    }
};
pub const error = error{
    InvalidToken,
    Expired,
};
