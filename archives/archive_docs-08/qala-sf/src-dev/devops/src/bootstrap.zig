// @license("MIT")
// @brief("")
// @author("qala development team")
// @copyright("2024 qala development team")
const std = @import("std");

pub const Stage = struct {
    name: []const u8,
    cmd: []const u8,
    cwd: []const u8,
    expected: []const u8, // expected SHA256
};

pub const BootstrapTool = struct {
    name: []const u8,
    seed: []const u8,
    stages: []Stage,
};

pub const BootstrapManifest = struct {
    tools: []BootstrapTool,
};

pub fn loadBootstrapManifest(
    allocator: std.mem.Allocator,
) !BootstrapManifest {
    var cwd = std.fs.cwd();
    const text = try cwd.readFileAlloc(
        allocator,
        ".ci_toolchain/bootstrap.json",
        128 * 1024,
    );

    var parser = std.json.Parser.init(allocator, false);
    defer parser.deinit();

    const root = try parser.parse(text);
    const arr = root.object.get("bootstrap").?.array;

    var tools = std.ArrayList(BootstrapTool).init(allocator);

    for (arr.items) |tbl| {
        const seed = tbl.object.get("seed").?.string;
        const name = tbl.object.get("name").?.string;

        const stages_arr = tbl.object.get("stages").?.array;
        var stages = std.ArrayList(Stage).init(allocator);

        for (stages_arr.items) |st| {
            try stages.append(.{
                .name = st.object.get("name").?.string,
                .cmd = st.object.get("cmd").?.string,
                .cwd = st.object.get("cwd").?.string,
                .expected = st.object.get("expected").?.string,
            });
        }

        try tools.append(.{
            .name = name,
            .seed = seed,
            .stages = try stages.toOwnedSlice(),
        });
    }

    return BootstrapManifest{
        .tools = try tools.toOwnedSlice(),
    };
}

pub fn runBootstrap(
    allocator: std.mem.Allocator,
    manifest: BootstrapManifest,
) !void {
    const stdout = std.io.getStdOut().writer();

    for (manifest.tools) |tool| {
        try stdout.print("Bootstrapping tool: {s}\n", .{tool.name});

        var last_output: []const u8 = tool.seed;

        for (tool.stages) |stage| {
            try stdout.print("  → Stage: {s}\n", .{stage.name});

            var child = std.ChildProcess.init(
                &.{ "/bin/sh", "-c", stage.cmd },
                allocator,
            );
            child.cwd = stage.cwd;
            child.stdin_behavior = .Inherit;
            child.stdout_behavior = .Inherit;
            child.stderr_behavior = .Inherit;
            try child.spawnAndWait();

            // Read stage output binary
            const out_bin = try std.fs.cwd().readFileAlloc(
                allocator,
                last_output,
                64 * 1024 * 1024,
            );

            // Hash
            var hasher = std.crypto.hash.sha256.Sha256.init(.{});
            hasher.update(out_bin);
            const digest = hasher.finalResult();

            var hex: [64]u8 = undefined;
            _ = std.fmt.bufPrint(&hex, "{x}", .{digest}) catch unreachable;

            if (!std.mem.eql(u8, hex[0..], stage.expected)) {
                return error.VerificationFailed;
            }

            try stdout.print("    ✓ Verified output hash\n", .{});
        }
    }
}
pub const error = struct {
    VerificationFailed: error{VerificationFailed},
};