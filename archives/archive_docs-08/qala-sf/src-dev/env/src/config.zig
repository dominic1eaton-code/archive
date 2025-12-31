// @license("MIT")
// @brief("")
// @author("qala development team")
// @copyright("2024 qala development team")
const std = @import("std");

pub const Entry = struct {
    name: []const u8,
    value: []const u8,
};

pub const Section = struct {
    name: []const u8,
    entries: std.ArrayList(Entry),
};

pub const Config = struct {
    allocator: std.mem.Allocator,
    sections: std.ArrayList(Section),

    pub fn init(allocator: std.mem.Allocator) Config {
        return Config{
            .allocator = allocator,
            .sections = std.ArrayList(Section).init(allocator),
        };
    }

    pub fn deinit(self: *Config) void {
        for (self.sections.items) |*s| {
            s.entries.deinit();
        }
        self.sections.deinit();
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

            if (line[0] == '[' and line[line.len - 1] == ']') {
                const name = line[1 .. line.len - 1];
                var section = Section{
                    .name = name,
                    .entries = std.ArrayList(Entry).init(self.allocator),
                };
                try self.sections.append(section);
                current_section = &self.sections.items[self.sections.items.len - 1];
                continue;
            }

            if (current_section) |sec| {
                if (std.mem.indexOf(u8, line, "=")) |eq| {
                    const key = std.mem.trim(u8, line[0..eq], " \t");
                    const value = std.mem.trim(u8, line[eq + 1 ..], " \t\"");

                    try sec.entries.append(.{
                        .name = key,
                        .value = value,
                    });
                }
            }
        }
    }

    pub fn get(self: *Config, section_name: []const u8, key_name: []const u8) ?[]const u8 {
        for (self.sections.items) |sec| {
            if (std.mem.eql(u8, sec.name, section_name)) {
                for (sec.entries.items) |e| {
                    if (std.mem.eql(u8, e.name, key_name))
                        return e.value;
                }
            }
        }
        return null;
    }
};
