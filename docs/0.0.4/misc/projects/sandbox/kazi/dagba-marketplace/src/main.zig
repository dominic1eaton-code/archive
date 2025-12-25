// @copyright
// @brief main entry point
// @note
const std = @import("std");

pub fn main() !void {
    try Command.start();
}

const Command = struct {
    fn start() !void {
        std.debug.print("starting node!\n", .{});
        const Node = NodeType();
        var node: Node = undefined;
        try node.open();
        while (true) {
            try node.tick();
        }
    }
};

pub fn NodeType() type {
    return struct {
        const Node = @This();

        initialized: bool,

        count: i64,

        pub fn open(self: *Node) !void {
            std.debug.print("opening node\n", .{});
            self.initialized = true;
        }

        pub fn tick(self: *Node) !void {
            std.debug.print("tick!\n", .{});
            self.count = 0;
        }
    };
}
