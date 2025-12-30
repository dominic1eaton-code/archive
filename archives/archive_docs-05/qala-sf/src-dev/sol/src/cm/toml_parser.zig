const std = @import("std");
const json = std.json;

pub fn parseTOML(allocator: *std.mem.Allocator, text: []const u8) !json.Value {
    var root = json.Value.initObject(allocator) catch return error.AllocFailed;
    var current_table: *json.Value = &root;

    var lines_it = std.mem.split(text, "\n");
    for (lines_it) |line| {
        const trimmed = std.mem.trim(line, " \t");
        if (trimmed.len == 0 or trimmed[0] == '#') continue;

        // Table header
        if (trimmed[0] == '[' and trimmed[trimmed.len - 1] == ']') {
            const table_name = trimmed[1..trimmed.len - 1];
            current_table = root.Object.get(table_name) orelse {
                const new_table = json.Value.initObject(allocator) catch return error.AllocFailed;
                try root.Object.put(table_name, new_table);
                root.Object.get(table_name) orelse return error.InvalidTOML
            };
            continue;
        }

        // Key = value
        const kv_it = std.mem.split(trimmed, "=");
        const key_raw = kv_it.next() orelse return error.InvalidTOML;
        const value_raw = kv_it.next() orelse return error.InvalidTOML;

        const key = std.mem.trim(key_raw, " \t");
        const value_str = std.mem.trim(value_raw, " \t");

        const parsed_value = try parseValue(allocator, value_str);
        try current_table.Object.put(key, parsed_value);
    }

    return root;
}

// Parse individual TOML value
fn parseValue(allocator: *std.mem.Allocator, value: []const u8) !json.Value {
    // String
    if (std.mem.startsWith(value, "\"") and std.mem.endsWith(value, "\"")) {
        return json.Value{ .String = value[1..value.len - 1] };
    }

    // Bool
    if (std.mem.eql(u8, value, "true")) return json.Value{ .Bool = true };
    if (std.mem.eql(u8, value, "false")) return json.Value{ .Bool = false };

    // Int
    if (std.fmt.parseInt(i64, value, 10)) |v| return json.Value{ .Int = v };

    // Float
    if (std.fmt.parseFloat(f64, value, 10)) |v| return json.Value{ .Float = v };

    // Array (including nested arrays)
    if (std.mem.startsWith(value, "[") and std.mem.endsWith(value, "]")) {
        const arr_content = value[1..value.len - 1];
        var arr = std.ArrayList(json.Value).init(allocator);

        var depth: usize = 0;
        var start: usize = 0;
        for (arr_content) |c, i| {
            if (c == '[') depth += 1;
            else if (c == ']') depth -= 1;
            else if (c == ',' and depth == 0) {
                const item = std.mem.trim(arr_content[start..i], " \t");
                if (item.len > 0) try arr.append(try parseValue(allocator, item));
                start = i + 1;
            }
        }
        // Last item
        const last_item = std.mem.trim(arr_content[start..], " \t");
        if (last_item.len > 0) try arr.append(try parseValue(allocator, last_item));

        var val = json.Value{ .Array = arr.toOwnedSlice() };
        arr.deinit();
        return val;
    }

    // Inline table
    if (std.mem.startsWith(value, "{") and std.mem.endsWith(value, "}")) {
        const content = value[1..value.len - 1];
        var table = json.Value.initObject(allocator) catch return error.AllocFailed;
        const kv_pairs = std.mem.split(content, ",");
        for (kv_pairs) |kv| {
            const pair = std.mem.split(kv, "=");
            const k = std.mem.trim(pair.next() orelse return error.InvalidTOML, " \t");
            const v = std.mem.trim(pair.next() orelse return error.InvalidTOML, " \t");
            const parsed = try parseValue(allocator, v);
            try table.Object.put(k, parsed);
        }
        return table;
    }

    return error.InvalidTOML;
}


pub fn parseTOML(allocator: *std.mem.Allocator, text: []const u8) !json.Value {
    var root = json.Value.initObject(allocator) catch return error.AllocFailed;
    var current_table: *json.Value = &root;

    var lines_it = std.mem.split(text, "\n");

    for (lines_it) |line| {
        const trimmed = std.mem.trim(line, " \t");
        if (trimmed.len == 0 or trimmed[0] == '#') continue;

        // Table header
        if (trimmed[0] == '[' and trimmed[trimmed.len - 1] == ']') {
            const table_name = trimmed[1..trimmed.len - 1];
            current_table = root.Object.get(table_name) orelse {
                const new_table = json.Value.initObject(allocator) catch return error.AllocFailed;
                try root.Object.put(table_name, new_table);
                root.Object.get(table_name) orelse return error.InvalidTOML
            };
            continue;
        }

        // Key = value
        const kv_it = std.mem.split(trimmed, "=");
        const key_raw = kv_it.next() orelse return error.InvalidTOML;
        const value_raw = kv_it.next() orelse return error.InvalidTOML;

        const key = std.mem.trim(key_raw, " \t");
        const value_str = std.mem.trim(value_raw, " \t");

        const parsed_value = try parseValue(allocator, value_str);
        try current_table.Object.put(key, parsed_value);
    }

    return root;
}

// Parse individual TOML value
fn parseValue(allocator: *std.mem.Allocator, value: []const u8) !json.Value {
    // String
    if (std.mem.startsWith(value, "\"") and std.mem.endsWith(value, "\"")) {
        return json.Value{ .String = value[1..value.len - 1] };
    }

    // Bool
    if (std.mem.eql(u8, value, "true")) return json.Value{ .Bool = true };
    if (std.mem.eql(u8, value, "false")) return json.Value{ .Bool = false };

    // Int
    if (std.fmt.parseInt(i64, value, 10)) |v| return json.Value{ .Int = v };

    // Float
    if (std.fmt.parseFloat(f64, value, 10)) |v| return json.Value{ .Float = v };

    // Array
    if (std.mem.startsWith(value, "[") and std.mem.endsWith(value, "]")) {
        const arr_content = value[1..value.len - 1];
        var arr = std.ArrayList(json.Value).init(allocator);
        const items = std.mem.split(arr_content, ",");
        for (items) |item| {
            const trimmed_item = std.mem.trim(item, " \t");
            const parsed = try parseValue(allocator, trimmed_item);
            try arr.append(parsed);
        }
        var val = json.Value{ .Array = arr.toOwnedSlice() };
        arr.deinit();
        return val;
    }

    // Inline table
    if (std.mem.startsWith(value, "{") and std.mem.endsWith(value, "}")) {
        const content = value[1..value.len - 1];
        var table = json.Value.initObject(allocator) catch return error.AllocFailed;
        const kv_pairs = std.mem.split(content, ",");
        for (kv_pairs) |kv| {
            const pair = std.mem.split(kv, "=");
            const k = std.mem.trim(pair.next() orelse return error.InvalidTOML, " \t");
            const v = std.mem.trim(pair.next() orelse return error.InvalidTOML, " \t");
            const parsed = try parseValue(allocator, v);
            try table.Object.put(k, parsed);
        }
        return table;
    }

    return error.InvalidTOML;
}

pub fn serializeTOML(val: json.Value, writer: anytype) !void {
    try serializeTOMLInternal(val, writer, "", true);
}

fn serializeTOMLInternal(val: json.Value, writer: anytype, prefix: []const u8, top_level: bool) !void {
    switch (val.tag) {
        .Object => {
            // First serialize non-object entries
            for (val.Object) |entry| {
                const key = entry.key;
                const v = entry.value;
                if (v.tag != .Object) {
                    switch (v.tag) {
                        .String => try writer.print("{s} = \"{s}\"\n", .{ key, v.String }),
                        .Int => try writer.print("{s} = {d}\n", .{ key, v.Int }),
                        .Bool => try writer.print("{s} = {b}\n", .{ key, v.Bool }),
                        .Float => try writer.print("{s} = {f}\n", .{ key, v.Float }),
                        .Array => try serializeArrayInline(key, v, writer),
                        else => {},
                    }
                }
            }

            // Then serialize object entries as tables
            for (val.Object) |entry| {
                const key = entry.key;
                const val = entry.value;
                if (val.tag == .Object) {
                    if (!top_level) try writer.print("\n");
                    const full_prefix = if (prefix.len == 0) key else std.fmt.allocPrint(std.heap.page_allocator, "{s}.{s}", .{ prefix, key }) catch return;
                    try writer.print("[{s}]\n", .{full_prefix});
                    try serializeTOMLInternal(val, writer, full_prefix, false);
                }
            }
        },
        else => {},
    }
}