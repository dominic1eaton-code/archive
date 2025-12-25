// @license("MIT")
// @brief("")
// @author("qala development team")
// @copyright("2024 qala development team")
const std = @import("std");
const writeCanonicalJson = @import("json.zig").writeCanonicalJson;

pub const OutputFile = struct {
    file: []const u8,
    digest: []const u8,
    size: usize,
};

pub const Step = struct {
    command: []const u8,
    env: [][]const u8,
};

pub const Attestation = struct {
    job: []const u8,
    action_hash: []const u8,
    steps: []Step,
    toolchain_json: []const u8,
    inputs_workspace_hash: []const u8,
    inputs_deps: [][]const u8,
    outputs: []OutputFile,
    timestamp: u64,
    sandbox_json: []const u8,
};

pub fn computeAttestationHash(
    allocator: std.mem.Allocator,
    at: Attestation,
) ![]u8 {
    var buf = std.ArrayList(u8).init(allocator);
    defer buf.deinit();

    var w = buf.writer();
    try writeCanonicalJson(at, w);

    var hasher = std.crypto.hash.sha256.Sha256.init(.{});
    hasher.update(buf.items);

    const digest = hasher.finalResult();
    return std.fmt.allocPrint(allocator, "sha256:{x}", .{digest});
}

pub fn signAttestation(
    allocator: std.mem.Allocator,
    at_json: []const u8,
    private_key_path: []const u8,
) ![]u8 {
    var key_file = try std.fs.cwd().openFile(private_key_path, .{});
    defer key_file.close();

    var priv: [64]u8 = undefined;
    _ = try key_file.readAll(&priv);

    var signer = std.crypto.sign.Ed25519{ .secret_key = priv };
    const sig = try signer.sign(at_json, allocator);

    return sig;
}

pub fn verifyAttestation(
    at_json: []const u8,
    sig: []const u8,
    public_key_path: []const u8,
) !void {
    var f = try std.fs.cwd().openFile(public_key_path, .{});
    defer f.close();

    var pub: [32]u8 = undefined;
    _ = try f.readAll(&pub);

    var verifier = std.crypto.sign.Ed25519{ .public_key = pub };
    try verifier.verify(sig, at_json);
}

// Build the attestation struct:
const att = Attestation{
    .job = job.name,
    .action_hash = action_hash,
    .steps = steps_array,
    .toolchain_json = toolchain_json,
    .inputs_workspace_hash = workspace_hash,
    .inputs_deps = deps_list,
    .outputs = outputs_list,
    .timestamp = 0, // deterministic
    .sandbox_json = sandbox_description,
};

// Serialize
var buf = std.ArrayList(u8).init(allocator);
var w = buf.writer();
try writeCanonicalJson(att, w);

// Compute hash
const att_hash = try computeAttestationHash(allocator, att);

// Save JSON
const p = try std.fmt.allocPrint(allocator,
    "ci_attestations/{s}-{s}.json",
    .{ job.name, att_hash }
);
try std.fs.cwd().writeFile(p, buf.items);

// Sign
const sig = try signAttestation(
    allocator,
    buf.items,
    "ci_keys/attestation_key.ed25519",
);

// Save sig
const sp = try std.fmt.allocPrint(allocator,
    "ci_attestations/{s}-{s}.sig",
    .{ job.name, att_hash }
);
try std.fs.cwd().writeFile(sp, sig);
