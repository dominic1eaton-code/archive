const std = @import("std");
const json = std.json;

pub fn serializeTOML(value: json.Value, writer: anytype) !void {
    try serializeTOMLInternal(value, writer, "", false);
}

fn serializeTOMLInternal(value: json.Value, writer: anytype, prefix: []const u8, top_level: bool) !void {
    switch (value.tag) {
        .Object => |obj| {
            // First, print top-level key-values (strings, ints, bools)
            for (obj.Object) |entry| {
                const key = entry.key;
                const val = entry.value;
                switch (val.tag) {
                    .Object => {},
                    .String => try writer.print("{s} = \"{s}\"\n", .{ key, val.String }),
                    .Int => try writer.print("{s} = {d}\n", .{ key, val.Int }),
                    .Bool => try writer.print("{s} = {b}\n", .{ key, val.Bool }),
                    .Float => try writer.print("{s} = {f}\n", .{ key, val.Float }),
                    else => {},
                }
            }

            // Now handle nested objects as tables
            for (obj.Object) |entry| {
                const key = entry.key;
                const val = entry.value;
                if (val.tag == .Object) {
                    if (!top_level) try writer.print("\n");
                    if (prefix.len == 0) {
                        try writer.print("[{s}]\n", .{key});
                        try serializeTOMLInternal(val, writer, key, false);
                    } else {
                        const new_prefix = std.fmt.allocPrint(std.heap.page_allocator, "{s}.{s}", .{ prefix, key }) catch return;
                        try writer.print("[{s}]\n", .{new_prefix});
                        try serializeTOMLInternal(val, writer, new_prefix, false);
                    }
                }
            }
        },
        else => {},
    }
}

pub fn load(path: []const u8, allocator: std.mem.Allocator) !Config {
    const file = try std.fs.cwd().openFile(path, .{ .read = true });
    defer file.close();
    const file_size = try file.getEndPos();
    var buffer = try allocator.alloc(u8, file_size);
    defer allocator.free(buffer);
    try file.readAll(buffer);
    const parser = json.Parser.init(allocator, buffer);
    const value = try parser.parse();
    return Config{ .data = value };
}

pub fn serializeTOML(value: json.Value, writer: anytype) !void {
    try serializeTOMLInternal(value, writer, "", true);
}

fn serializeTOMLInternal(value: json.Value, writer: anytype, prefix: []const u8, top_level: bool) !void {
    switch (value.tag) {
        .Object => |obj| {
            // 1. Print primitive key-values first (strings, ints, bools, floats)
            for (obj.Object) |entry| {
                const key = entry.key;
                const val = entry.value;
                switch (val.tag) {
                    .Object => {},
                    .String => try writer.print("{s} = \"{s}\"\n", .{ key, val.String }),
                    .Int => try writer.print("{s} = {d}\n", .{ key, val.Int }),
                    .Bool => try writer.print("{s} = {b}\n", .{ key, val.Bool }),
                    .Float => try writer.print("{s} = {f}\n", .{ key, val.Float }),
                    .Array => try serializeArrayInline(key, val, writer),
                    else => {},
                }
            }

            // 2. Now handle nested tables as `[table]` headers
            for (obj.Object) |entry| {
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

// Helper: serialize arrays inline
fn serializeArrayInline(key: []const u8, val: json.Value, writer: anytype) !void {
    if (val.tag != .Array) return;

    try writer.print("{s} = [", .{key});
    var first = true;
    for (val.Array) |elem| {
        if (!first) try writer.print(", ", .{});
        first = false;
        switch (elem.tag) {
            .String => try writer.print("\"{s}\"", .{elem.String}),
            .Int => try writer.print("{d}", .{elem.Int}),
            .Bool => try writer.print("{b}", .{elem.Bool}),
            .Float => try writer.print("{f}", .{elem.Float}),
            .Object => try serializeInlineTable(elem, writer),
            else => {},
        }
    }
    try writer.print("]\n", .{});
}

// Helper: serialize an inline table
fn serializeInlineTable(val: json.Value, writer: anytype) !void {
    if (val.tag != .Object) return;

    try writer.print("{{", .{});
    var first = true;
    for (val.Object) |entry| {
        if (!first) try writer.print(", ", .{});
        first = false;
        const k = entry.key;
        const v = entry.value;
        switch (v.tag) {
            .String => try writer.print("{s} = \"{s}\"", .{ k, v.String }),
            .Int => try writer.print("{s} = {d}", .{ k, v.Int }),
            .Bool => try writer.print("{s} = {b}", .{ k, v.Bool }),
            .Float => try writer.print("{s} = {f}", .{ k, v.Float }),
            else => {},
        }
    }
    try writer.print("}}", .{});
}

fn serializeArrayInline(key: []const u8, val: json.Value, writer: anytype) !void {
    if (val.tag != .Array) return;

    try writer.print("{s} = [", .{key});
    var first = true;
    for (val.Array) |elem| {
        if (!first) try writer.print(", ", .{});
        first = false;
        switch (elem.tag) {
            .String => try writer.print("\"{s}\"", .{elem.String}),
            .Int => try writer.print("{d}", .{elem.Int}),
            .Bool => try writer.print("{b}", .{elem.Bool}),
            .Float => try writer.print("{f}", .{elem.Float}),
            .Array => try serializeArrayInlineInline(elem, writer),
            .Object => try serializeInlineTable(elem, writer),
            else => {},
        }
    }
    try writer.print("]\n", .{});
}

fn serializeArrayInlineInline(val: json.Value, writer: anytype) !void {
    if (val.tag != .Array) return;
    try writer.print("[", .{});
    var first = true;
    for (val.Array) |elem| {
        if (!first) try writer.print(", ", .{});
        first = false;
        switch (elem.tag) {
            .String => try writer.print("\"{s}\"", .{elem.String}),
            .Int => try writer.print("{d}", .{elem.Int}),
            .Bool => try writer.print("{b}", .{elem.Bool}),
            .Float => try writer.print("{f}", .{elem.Float}),
            .Array => try serializeArrayInlineInline(elem, writer),
            .Object => try serializeInlineTable(elem, writer),
            else => {},
        }
    }
    try writer.print("]", .{});
}

pub fn main() !void {
    const allocator = std.heap.page_allocator;

    var config = try Config.load("config.toml", allocator);

    const db_host = config.getString("database.host") orelse "localhost";
    std.debug.print("DB Host: {s}\n", .{db_host});

    // Update a value
    try config.setString("database.host", "192.168.1.50");

    // Save as TOML (with arrays and inline tables preserved)
    try config.saveTOML();
}
