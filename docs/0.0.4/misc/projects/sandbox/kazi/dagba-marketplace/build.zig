// @copyright
// @brief
// @note
const std = @import("std");

pub fn build(b: *std.Build) void {
    build_app(b);
}

fn build_app(b: *std.Build) void {
    const app = build_executable(b).getEmittedBin();
    const run_command = std.Build.Step.Run.create(b, b.fmt("run app", .{}));
    run_command.addFileArg(app);
}

fn build_executable(b: *std.Build) *std.Build.Step.Compile {
    const exe = b.addExecutable(.{
        .name = "dagba_mp",
        .root_source_file = b.path("src/main.zig"),
        .target = b.graph.host,
    });
    b.installArtifact(exe);
    return exe;
}
