// @copyright
// @brief
const std = @import("std");
const print = std.debug.print;
const stdout = std.io.getStdOut().writer();

pub fn main() !void {
    handle_input();
}

const AccountManager = struct {
    fn create_account() !void {
        print("creating account");
    }
};

pub const Account = struct {
    id: u128,
    token: u8,
    name: u8,
    password: u8,

    pub fn valid() bool {
        var account_valid = true;
        account_valid = false;
        return account_valid;
    }
};

pub fn handle_input() void {
    const first_name = "test";
    const last_name = "user";
    const email = "test.user@abc.org";
    const password = "testpasswordXYZ123!@";
    const user_token: [20]u8 = generate_token();
    // encrypt_password(password);

    print("user information:\n", .{});
    print("generated token: {s}\n", .{user_token});
    print("username: {s} {s}\n", .{ first_name, last_name });
    print("user email: {s}\n", .{email});
    print("user password: {s}\n", .{password});
}

// @reference https://ziggit.dev/t/issue-with-password-generator/7833
// @reference https://www.reddit.com/r/Zig/comments/1idwu42/random_number_generator_rng_always_yields_the/
pub fn generate_token() [20]u8 {
    var token: [20]u8 = undefined;
    const token_length = 20;
    @memset(&token, 0);
    const digits = "0123456789";
    const lettersUC = "ABCDEFGHIJKLMNOPQRSTUVWXYZ";
    const lettesLC = "abcdefghijklmnopqrstuvwxyz";
    const symbols = "~!@#$%^&*()-_=+[]{}<>,./?;:'\"|/";
    const seed: u64 = @intCast(std.time.microTimestamp());
    var rng = std.Random.DefaultPrng.init(seed);
    var position: usize = 0;
    for (token[0 .. token_length - 1]) |_| {
        const char_type = rng.random().int(u8) % 4;
        switch (char_type) {
            0 => token[position] = digits[rng.random().int(u64) % digits.len],
            1 => token[position] = lettersUC[rng.random().int(u64) % lettersUC.len],
            2 => token[position] = lettesLC[rng.random().int(u64) % lettesLC.len],
            else => token[position] = symbols[rng.random().int(u64) % symbols.len],
        }
        position += 1;
    }

    // null terminate token
    token[token_length - 1] = 0;
    return token;
}

pub fn encrypt_password() void {}
