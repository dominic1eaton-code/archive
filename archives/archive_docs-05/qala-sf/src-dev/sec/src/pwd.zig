const std = @import("std");

pub fn hashPassword(
    allocator: *std.mem.Allocator,
    password: []const u8,
) ![]u8 {
    // Argon2id defaults — memory‑hard, suitable for password storage
    const hashed = try std.crypto.pwhash.argon2.strHash(
        password,
        std.crypto.pwhash.argon2.HashOptions{
            .allocator = allocator,
            .params = .{}, // defaults (secure)
            .encoding = .phc,
        },
    );
    return hashed;
}

pub fn verifyPassword(
    alloc: *std.mem.Allocator,
    stored_hash: []const u8,
    password: []const u8,
) !bool {
    return std.crypto.pwhash.argon2.strVerify(
        stored_hash,
        password,
        std.crypto.pwhash.argon2.VerifyOptions{ .allocator = alloc },
    );
}
