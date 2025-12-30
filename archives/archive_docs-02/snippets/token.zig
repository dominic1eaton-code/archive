// @copyright
// @brief
// @reference https://ziggit.dev/t/issue-with-password-generator/7833
const std = @import("std");
const print = std.debug.print;
const rndgen = std.rand.DefaultPrng;

pub fn main() !void {
    const first_name = "test";
    const last_name = "user";
    const user_token: [10]u8 = generate_token(10);

    print("{s} {}\n", .{ first_name, @TypeOf(first_name) });
    print("{s} {}\n", .{ last_name, @TypeOf(last_name) });
    print("{s} {}\n", .{ user_token, @TypeOf(user_token) });

    //
}

pub fn generate_token(length: usize) []u8 {
    var token: [10]u8 = undefined;
    const letters = [26]u8{ 'a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j', 'k', 'l', 'm', 'n', 'o', 'p', 'q', 'r', 's', 't', 'u', 'v', 'w', 'x', 'y', 'z' };
    const symbols = [23]u8{ '~', '!', '@', '#', '$', '%', '^', '&', '*', '(', ')', '-', '_', '=', '+', '?', '<', '>', ':', ';', '\'', '"', '\\' };
    const letters_count: u8 = 26;
    const symbols_count: u8 = 23;
    var tval: bool = false;
    if (length == 10) {
        tval = true;
    }

    @memset(&token, 0);
    // var token = std.mem.zeroes([length]u8);
    // var token_count: usize = 0;
    var rnd = rndgen.init(0);

    for (token) |elem| {
        const rand = rnd.random();
        const position = rand.intRangeAtMost(u8, 0, letters_count + symbols_count);
        if (position >= letters_count) {
            elem = letters[position];
        } else {
            elem = symbols[position];
        }
    }
    return token;
}

pub fn main2() !void {
    const user_token: [10]u8 = generate_token();
    print("{s}\n", .{user_token});
}

// @reference https://ziggit.dev/t/issue-with-password-generator/7833
// @reference https://www.reddit.com/r/Zig/comments/1idwu42/random_number_generator_rng_always_yields_the/
pub fn generate_token2() [10]u8 {
    var token: [10]u8 = undefined;
    @memset(&token, 0);
    // const letters_uc = "ABCDEFGHIJKLMNOPQRSTUVWXYZ";
    // const letters_lc = "abcdefghijklmnopqrstuvwxyz";
    // const digits = "0123456789";
    // const symbols = "~!@#$%^&*()-_=+[]{}<>,./?;:'\"|/";
    // var seed = @intCast(u64, std.time.microTimestamp());
    const seed: u64 = @intCast(std.time.microTimestamp());
    var rng = std.Random.DefaultPrng.init(seed);
    // const rnd = std.Random.DefaultPrng.init(blk: {
    //     var seed: u64 = undefined;
    //     try std.posix.getrandom(std.mem.asBytes(&seed));
    //     break :blk seed;
    // });

    // print("{d}\n", .{rng.random().int(u8)});
    // try stdout.print("generated token: {s}\n", .{token});

    print("{d}\n", .{rng.random().int(u8)});
    return token;
}
