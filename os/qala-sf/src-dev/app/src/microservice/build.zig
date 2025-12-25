const std = @import("std");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

    const exe = b.addExecutable(.{
        .name = "app-service",
        .target = target,
        .optimize = optimize,
        .root_source_file = .{ .path = "src/main.zig" },
    });

    exe.addIncludePath(.{ .path = "/usr/include" });
    exe.linkSystemLibrary("c");
    exe.linkSystemLibrary("rdkafka");

    exe.addPackage(.{
        .name = "postgres",
        .path = .{ .path = "deps/rpostgresql/src/lib.zig" },
    });

    exe.addPackage(.{
        .name = "grpc_zig",
        .path = .{ .path = "deps/grpc-zig/src/lib.zig" },
    });

    b.installArtifact(exe);
}

const std = @import("std");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

    const exe = b.addExecutable(.{
        .name = "api-gateway",
        .root_source_file = .{ .path = "src/main.zig" },
        .target = target,
        .optimize = optimize,
    });

    exe.addPackage(.{
        .name = "grpc_zig",
        .path = .{ .path = "deps/grpc-zig/src/lib.zig" },
    });

    exe.addPackage(.{
        .name = "postgres",
        .path = .{ .path = "../app-service/deps/rpostgresql/src/lib.zig" },
    });

    const exe = b.addExecutable(.{
        .name = "worker-service",
        .root_source_file = .{ .path = "src/main.zig" },
        .target = target,
        .optimize = optimize,
    });

    exe.addIncludePath(.{ .path = "/usr/include" });
    exe.linkSystemLibrary("c");
    exe.linkSystemLibrary("rdkafka");

    exe.addPackage(.{
        .name = "postgres",
        .path = .{ .path = "../app-service/deps/rpostgresql/src/lib.zig" },
    });

    exe.linkSystemLibrary("c");

    b.installArtifact(exe);
}
