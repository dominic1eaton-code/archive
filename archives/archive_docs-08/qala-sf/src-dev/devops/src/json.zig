// @license("MIT")
// @brief("")
// @author("qala development team")
// @copyright("2024 qala development team")

pub fn writeCanonicalJson(
    at: Attestation,
    w: anytype,
) !void {
    try w.print(
        "{{\"job\":\"{s}\",\"action_hash\":\"{s}\",",
        .{ at.job, at.action_hash },
    );

    // Steps
    try w.print("\"steps\":[", .{});
    for (at.steps, 0..) |st, i| {
        if (i != 0) try w.print(",", .{});
        try w.print("{{\"command\":\"{s}\",\"environment\":{{", .{st.command});

        for (st.env, 0..) |ev, j| {
            if (j != 0) try w.print(",", .{});
            const eq = std.mem.indexOfScalar(u8, ev, '=') orelse continue;
            const key = ev[0..eq];
            const val = ev[eq + 1 ..];
            try w.print("\"{s}\":\"{s}\"", .{ key, val });
        }
        try w.print("}}}}", .{});
    }
    try w.print("],", .{});

    // Toolchain
    try w.print("\"toolchain\":{s},", .{at.toolchain_json});

    // Inputs
    try w.print("\"inputs\":{{\"workspace_hash\":\"{s}\",\"dependencies\":[", .{at.inputs_workspace_hash});
    for (at.inputs_deps, 0..) |d, k| {
        if (k != 0) try w.print(",", .{});
        try w.print("\"{s}\"", .{d});
    }
    try w.print("]}},", .{});

    // Outputs
    try w.print("\"outputs\":[", .{});
    for (at.outputs, 0..) |f, i| {
        if (i != 0) try w.print(",", .{});
        try w.print("{{\"file\":\"{s}\",\"digest\":\"{s}\",\"size\":{}}}", .{ f.file, f.digest, f.size });
    }
    try w.print("],", .{});

    // Timestamp
    try w.print("\"timestamp\":{},", .{at.timestamp});

    // Sandbox
    try w.print("\"sandbox\":{s}", .{at.sandbox_json});

    try w.print("}}", .{});
}

