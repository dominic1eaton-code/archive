# software configuration/release management system
add Support JSON storage for structured release info

Add deployment simulation (or integrate with Git, Docker, etc.)

Add rollback functionality

Add version validation and semantic versioning support

Add tagging or environment (staging/production) info

add proper version history




✅ Features Implemented

JSON storage for structured release info

Semantic version validation

Environment support (staging/production)

Version history (previous releases in JSON)

Deploy simulation

Rollback to the previous release

Basic tags structure ready (optional field)



✅ Features Now Included

Automatic version increment (patch, minor, major)

Git integration (commit, tag, push)

Docker integration (build and deploy containerized release)

Interactive CLI prompts for release creation

Maintains version history in JSON

Supports rollback, tags, environments

## configuration management system
How it works:

Config.load() reads the JSON file and parses it.

getString, getInt, getBool allow type-safe access to configuration values

✅ This system now supports:

Nested keys via "database.host".

Reading/writing JSON.

Basic TOML parsing for initial loading.

Modifying values and saving them back.

Features now

Nested keys with dot notation, e.g., "database.host".

Read/write JSON for backward compatibility.

Read/write TOML with proper tables and nested tables.

Human-readable TOML output with tables grouped correctly.

Supports string, int, bool, float.

✅ Features Now

Read TOML fully with arrays and inline tables.

Supports nested tables and nested inline tables.

Works with strings, ints, floats, booleans, arrays, inline tables.

Fully compatible with the existing TOML serializer.

<code>
const std = @import("std");
const Config = @import("config").Config;

pub fn main() !void {
    const allocator = std.heap.page_allocator;

    var config = try Config.loadTOML("config.toml", allocator);

    const matrix_val = config.traverseNested("matrix") orelse null;
    if (matrix_val) |m| {
        std.debug.print("Matrix:\n", .{});
        for (m.Array) |row| {
            if (row.tag == .Array) {
                for (row.Array) |v| {
                    if (v.tag == .Int) std.debug.print("{d} ", .{v.Int});
                }
                std.debug.print("\n", .{});
            }
        }
    }

    // Save changes back to TOML
    try config.saveTOML();
}
</code>

✅ Now your Zig Config Manager supports:

Nested keys via dot notation (database.host)

Nested tables [table]

Arrays, including nested arrays

Mixed-type arrays

Inline tables { key = value }

Round-trip TOML read → modify → save