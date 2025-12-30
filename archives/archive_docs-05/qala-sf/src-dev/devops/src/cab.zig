// @license("MIT")
// @brief("")
// @author("qala development team")
// @copyright("2024 qala development team")
pub fn writeCab(
    allocator: std.mem.Allocator,
    out_path: []const u8,
    files: []const struct {
        name: []const u8,
        data: []const u8,
    },
) !void {
    var out = try std.fs.cwd().createFile(out_path, .{});
    defer out.close();

    // Header
    try out.writer().print("CAB0", .{}); // magic
    try out.writer().print("{u32}", .{1}); // version
    try out.writer().print("{u32}", .{files.len});

    var offset: u64 = 16 + files.len * (256 + 16 + 32);

    // TOC entries
    for (files) |f| {
        var namebuf: [256]u8 = undefined;
        std.mem.copy(u8, namebuf[0..f.name.len], f.name);
        std.mem.set(u8, namebuf[f.name.len..], 0);
        try out.writeAll(&namebuf);

        try out.writer().print("{u64}{u64}", .{ offset, f.data.len });

        var h = std.crypto.hash.sha256.Sha256.init(.{});
        h.update(f.data);
        const digest = h.finalResult();
        try out.writeAll(&digest);

        offset += f.data.len;
    }

    // Payload
    for (files) |f| try out.writeAll(f.data);
}

const cab_name = try std.fmt.allocPrint(
    allocator,
    "artifact-bundles/{s}-{s}.cab",
    .{ job.name, artifact_hash }
);

try writeCab(allocator, cab_name, &[_]struct{
    name: []const u8, data: []const u8
}{
    .{ "artifact", artifact_bytes },
    .{ "attestation.json", att_json },
    .{ "attestation.sig", sig },
});

pub fn storeStepCache(
    allocator: std.mem.Allocator,
    job_name: []const u8,
    step_index: usize,
    hash: []const u8,
) !void {
    var h = std.crypto.hash.sha256.Sha256.init(.{});
    h.update(job_name);
    h.update(std.mem.asBytes(&step_index));
    h.update(hash);

    const digest = h.finalResult();

    var cwd = std.fs.cwd();
    var dir = try stepCacheDir(allocator, job_name, step_index);
    try cwd.createDirAll(dir, 0o755);

    var d = cwd.openDir(dir, .{});
    defer d.close();

    const name = try std.fmt.allocPrint(allocator, "{d}.hash", .{step_index});
    var file = try d.createFile(name, .{});
    defer file.close();

    try file.writeAll(digest[0..]);
}
//     var d = cwd.openDir(dir, .{});
//     defer d.close();

//     const name = try std.fmt.allocPrint(allocator, "{d}.hash", .{step_index});
//     var file = try d.createFile(name, .{});
//     defer file.close();

//     try file.writeAll(digest[0..]);
// }
//     try cwd.createDirAll(dir, 0o755);

//     var d = cwd.openDir(dir, .{});
//     defer d.close();

//     const name = try std.fmt.allocPrint(allocator, "{d}.hash", .{step_index});
//     var file = try d.createFile(name, .{});
//     defer file.close();

//     try file.writeAll(hash);
// }
