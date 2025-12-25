// @copyright
// @brief
const std = @import("std");
const print = std.debug.print;

pub fn prompt() void {
    const cout = std.io.getStdOut().writer();
    const cin = std.io.getStdIn().reader();
    const buffer_max_size = 1024;
    var terminate: bool = false;
    var buffer: [buffer_max_size]u8 = undefined;
    // std.mem.zeroes(&buffer);

    while (terminate != true) {
        try cout.print("> ", .{});
        @memset(&buffer, 0);
        const result = try cin.readUntilDelimiter(&buffer, '\n');
        _ = result;
        for (buffer) |character| {
            if (character == 'q') {
                terminate = true;
            }
        }
        try cout.print("{s}", .{buffer});
    }
}

pub const Account = struct {
    username: []u8,
    password: []u8,
    token: []u8,
    id: u128,
    email: []u8,
};

pub fn run_app() void {
    print("creating default account...");
    // const username: []u8 = "eatondo";
    // const password: []u8 = "abcd-1234";
    // const token: []u8 = "";

    print("creating default user portfolio");
}

pub fn main() !void {
    print("running app...", .{});
    // prompt();
}
