// @license("MIT")
// @brief("")
// @author("qala development team")
// @copyright("2024 qala development team")
const std = @import("std");

pub const MatchResult = enum {
    Match,
    Mismatch,
};

pub fn replayMatch(
    allocator: std.mem.Allocator,
    att_json: []const u8,
    current_action_hash: []const u8,
) !MatchResult {
    // Parse attestation into struct:
    var parser = std.json.Parser.init(allocator, false);
    defer parser.deinit();

    const root = try parser.parse(att_json);

    const att_hash = root.object.get("action_hash").?.string;

    if (!std.mem.eql(u8, att_hash, current_action_hash))
        return .Mismatch;

    return .Match;
}


pub fn load(self: *Config, path: []const u8) !void {
    var file = try std.fs.cwd().openFile(path, .{});
    defer file.close();
    const data = try file.readToEndAlloc(self.allocator, std.math.maxInt(usize));
    defer self.allocator.free(data);
    var it = std.mem.split(u8, data, "\n");
    var current_section: ?*Section = null;
    while (it.next()) |line_raw| {
        const line = std.mem.trim(u8, line_raw, " \t\r\n");
        if (line.len == 0 or line[0] == '#') continue;
        const eq_index = std.mem.indexOf(u8, line, '=');
        if (eq_index) |idx| {
            const name = std.mem.trim(u8, line[0..idx], " \t");
            const value = std.mem.trim(u8, line[idx + 1..], " \t");

            if (current_section) |s| {
                const entry = Entry{
                    .name = name,
                    .value = value,
                };
                try s.entries.append(entry);
            } else {
                return error.InvalidConfigFormat;
            }
        }
    }
     if (line[0] == '[' and line[line.len - 1] == ']') {
            const name = line[1 .. line.len - 1];
            var section = Section{
                .name = name,
                .entries = std.ArrayList(Entry).init(self.allocator),
            };
            try self.sections.append(section);
            current_section = &self.sections.items[self.sections.items.len - 1];
            continue;

            } else {
                return error.InvalidConfigFormat;
            }
        }
    };
    pub fn get(self: *Config, section_name: []const u8, key_name: []const u8) ?[]const u8 {
        for (self.sections.items) |sec| {
            if (std.mem.eql(u8, sec.name, section_name)) {
                for (sec.entries.items) |e| {
                    if (std.mem.eql(u8, e.name, key_name)) {
                        return e.value;
                    }
                }
            }
        }
        return null;
    }