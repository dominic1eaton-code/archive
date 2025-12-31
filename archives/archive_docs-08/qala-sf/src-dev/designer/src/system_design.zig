const std = @import("std");
const json = std.json;

const Alloc = std.mem.Allocator;

// -----------------------------
// Domain Model
// -----------------------------

pub const Component = struct {
    name: []const u8,
    kind: []const u8,           // "service", "database", "frontend", etc.
    interfaces: []const []const u8,
};

pub const Dependency = struct {
    from: []const u8,
    to: []const u8,
    kind: []const u8,           // "http", "rpc", "event", etc.
};

pub const SystemDesign = struct {
    components: []Component,
    dependencies: []Dependency,
};

// -----------------------------
// JSON Parsing
// -----------------------------

fn parseDesign(allocator: *Alloc, path: []const u8) !SystemDesign {
    const cwd = std.fs.cwd();
    const file = try cwd.openFile(path, .{});
    defer file.close();

    const data = try file.readToEndAlloc(allocator, 4096);
    defer allocator.free(data);

    var parser = json.Parser.init(data);
    const root = try parser.parseRoot();

    const obj = root.Object() orelse return error.InvalidFormat;

    const comps_node = obj.get("components").Array() orelse return error.InvalidFormat;
    const deps_node = obj.get("dependencies").Array() orelse return error.InvalidFormat;

    var components = try allocator.alloc(Component, comps_node.items().len);
    var dependencies = try allocator.alloc(Dependency, deps_node.items().len);

    // Parse components
    for (comps_node.items()) |item, i| {
        const o = item.Object() orelse return error.InvalidFormat;

        components[i] = Component{
            .name = o.get("name").String() orelse "",
            .kind = o.get("kind").String() orelse "",
            .interfaces = blk: {
                if (o.get("interfaces")) |n| {
                    const arr = n.Array() orelse &.{};
                    var list = try allocator.alloc([]const u8, arr.items().len);
                    for (arr.items()) |it, j| {
                        list[j] = it.String() orelse "";
                    }
                    break :blk list;
                } else break :blk &.{};
            },
        };
    }

    // Parse dependencies
    for (deps_node.items()) |item, i| {
        const o = item.Object() orelse return error.InvalidFormat;

        dependencies[i] = Dependency{
            .from = o.get("from").String() orelse "",
            .to   = o.get("to").String() orelse "",
            .kind = o.get("kind").String() orelse "",
        };
    }

    return SystemDesign{
        .components = components,
        .dependencies = dependencies,
    };
}

// -----------------------------
// Validation Rules
// -----------------------------

fn validateDesign(design: *const SystemDesign) !void {
    // Rule 1: Components must have unique names
    for (design.components) |c1, i| {
        for (design.components) |c2, j| {
            if (i != j and std.mem.eql(u8, c1.name, c2.name)) {
                std.debug.print("Error: Duplicate component name '{s}'.\n", .{c1.name});
                return error.DuplicateComponent;
            }
        }
    }

    // Rule 2: All dependency target components must exist
    for (design.dependencies) |d| {
        var found = false;
        for (design.components) |c| {
            if (std.mem.eql(u8, d.to, c.name)) {
                found = true;
                break;
            }
        }
        if (!found) {
            std.debug.print("Error: Dependency refers to unknown component '{s}'.\n", .{d.to});
            return error.UnknownComponent;
        }
    }

    // Rule 3: No circular dependencies (simple check)
    for (design.dependencies) |d1| {
        for (design.dependencies) |d2| {
            if (std.mem.eql(u8, d1.from, d2.to) and
                std.mem.eql(u8, d1.to, d2.from)) 
            {
                std.debug.print("Error: Circular dependency '{s}' <-> '{s}'.\n",
                    .{d1.from, d1.to});
                return error.CircularDependency;
            }
        }
    }
}

// -----------------------------
// Generation: Documentation Output
// -----------------------------

fn outputDesign(design: *const SystemDesign) void {
    std.debug.print("\n=== System Design Overview ===\n", .{});

    std.debug.print("\nComponents:\n", .{});
    for (design.components) |c| {
        std.debug.print(" - {s} ({s})\n", .{c.name, c.kind});
        if (c.interfaces.len > 0) {
            std.debug.print("    interfaces:\n", .{});
            for (c.interfaces) |iface|
                std.debug.print("      - {s}\n", .{iface});
        }
    }

    std.debug.print("\nDependencies:\n", .{});
    for (design.dependencies) |d| {
        std.debug.print(" - {s} -> {s} via {s}\n", .{d.from, d.to, d.kind});
    }
}

// -----------------------------
// CLI
// -----------------------------

fn printHelp() void {
    std.debug.print(
        \\Usage: ssads <command> [file]
        \\Commands:
        \\   load <file>    - load and validate a system design
        \\   show <file>    - load and display the design
        \\   help           - show this message
        \\
    , .{});
}

pub fn main() !void {
    const allocator = std.heap.page_allocator;
    var args = std.process.args();

    _ = args.next(); // skip program name

    if (args.next()) |cmd| {
        if (std.mem.eql(u8, cmd, "help")) {
            printHelp();
            return;
        }

        if (std.mem.eql(u8, cmd, "load")) {
            const file = args.next() orelse return;
            var design = try parseDesign(allocator, file);
            try validateDesign(&design);
            std.debug.print("Design '{s}' is valid.\n", .{file});
            return;
        }

        if (std.mem.eql(u8, cmd, "show")) {
            const file = args.next() orelse return;
            var design = try parseDesign(allocator, file);
            try validateDesign(&design);
            outputDesign(&design);
            return;
        }

        printHelp();
    } else {
        printHelp();
    }
}
