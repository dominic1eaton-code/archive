// @license("MIT")
// @brief("")
// @author("qala development team")
// @copyright("2024 qala development team")
pub fn logEntry(
    allocator: std.mem.Allocator,
    bundle_hash: []const u8,
    att_hash: []const u8,
    signature: []const u8,
    timestamp: u64,
) !void {
    var f = try std.fs.cwd().openFile("transparency-log/log.jsonl", .{
        .write = true,
        .append = true,
        .create = true,
    });
    defer f.close();

    try f.writer().print("{{\"bundle_hash\":\"{s}\",\"attestation_hash\":\"{s}\",\"signature\":\"{s}\",\"timestamp\":{}}}\n", .{ bundle_hash, att_hash, signature, timestamp });
}

// After .cab creation:
const bundle_hash = try sha256(cab_bytes);

try logEntry(
    allocator,
    bundle_hash,
    att_hash,
    sig_b64,
    0, // deterministic or trusted timestamp
);