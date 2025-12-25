const std = @import("std");

const User = struct {
    username: []const u8,
    token: []const u8,
};

pub const Auth = struct {
    users: []User,

    pub fn init(users: []User) Auth {
        return Auth{ .users = users };
    }

    pub fn authorize(self: *Auth, token: []const u8) bool {
        for (self.users) |u| {
            if (std.mem.eql(u8, u.token, token)) {
                return true;
            }
        }
        return false;
    }
};

pub const User = struct {
    username: []const u8,
    token: []const u8,
};

pub fn authenticate(token: []const u8, users: []User) bool {
    for (users) |user| {
        if (std.mem.eql(u8, token, user.token)) return true;
    }
    return false;
}
