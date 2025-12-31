// @license("MIT")
// @brief("app management system")
// @author("qala development team")
// @copyright("2024 qala development team")
const std = @import("std");

const App = struct {
    id: u32,
    name: []const u8,
    version: []const u8,
};

pub fn main() !void {
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    const allocator = &gpa.allocator;

    var apps: std.ArrayList(App) = std.ArrayList(App).init(allocator);

    var stdin = std.io.getStdIn().reader();
    var stdout = std.io.getStdOut().writer();
    var id_counter: u32 = 1;

    while (true) {
        try stdout.print("\nSoftware Management System:\n1. Add App\n2. List Apps\n3. Remove App\n4. Exit\nSelect an option: ", .{});
        const line = try stdin.readLineAlloc(allocator, 100);
        defer allocator.free(line);

        const option = std.fmt.parseInt(u32, line, 10) catch 0;

        switch (option) {
            1 => {
                try stdout.print("Enter app name: ", .{});
                const name_line = try stdin.readLineAlloc(allocator, 100);
                defer allocator.free(name_line);

                try stdout.print("Enter app version: ", .{});
                const version_line = try stdin.readLineAlloc(allocator, 100);
                defer allocator.free(version_line);

                const app = App{
                    .id = id_counter,
                    .name = name_line,
                    .version = version_line,
                };
                id_counter += 1;

                try apps.append(app);
                try stdout.print("App added successfully!\n", .{});
            },
            2 => {
                if (apps.items.len == 0) {
                    try stdout.print("No applications found.\n", .{});
                } else {
                    for (apps.items) |app| {
                        try stdout.print("ID: {d}, Name: {s}, Version: {s}\n", .{ app.id, app.name, app.version });
                    }
                }
            },
            3 => {
                try stdout.print("Enter App ID to remove: ", .{});
                const id_line = try stdin.readLineAlloc(allocator, 10);
                defer allocator.free(id_line);

                const remove_id = std.fmt.parseInt(u32, id_line, 10) catch 0;

                var removed = false;
                var i: usize = 0;
                while (i < apps.items.len) : (i += 1) {
                    if (apps.items[i].id == remove_id) {
                        apps.items.swapRemove(i);
                        removed = true;
                        break;
                    }
                }
                if (removed) {
                    try stdout.print("App removed successfully!\n", .{});
                } else {
                    try stdout.print("App ID not found.\n", .{});
                }
            },
            4 => {
                break;
            },
            else => {
                try stdout.print("Invalid option, try again.\n", .{});
            },
        }
    }

    apps.deinit();
}

test "app management system basic operations" {
    // This is a placeholder for potential future tests.
    // Currently, the main function handles interactive I/O,
    // which is not directly testable in this context.
}

fn loadApps(allocator: *std.mem.Allocator, path: []const u8) !std.ArrayList(App) {
    var apps: std.ArrayList(App) = std.ArrayList(App).init(allocator);
    const file_result = std.fs.cwd().openFile(path, .{ .read = true });
    if (file_result) |file| {
        defer file.close();
        const data = try file.readToEndAlloc(allocator, 1024);
        defer allocator.free(data);

        var parser = std.json.Parser.init(data);
        if (parser.next() catch null) |root| {
            if (root.getType() == .Array) {
                const array = root.Array();
                for (array.items) |item| {
                    const id = item.Object().get("id") orelse 0;
                    const name_json = item.Object().get("name") orelse "";
                    const version_json = item.Object().get("version") orelse "";

                    const app = App{
                        .id = @intCast(u32, id),
                        .name = name_json,
                        .version = version_json,
                    };
                    try apps.append(app);
                }
            }
        }
    }
    return apps;
}

fn saveApps(allocator: *std.mem.Allocator, path: []const u8, apps: *std.ArrayList(App)) !void {
    const file = try std.fs.cwd().createFile(path, .{ .truncate = true, .write = true });
    defer file.close();

    var json_array = try std.json.ArrayWriter.init(allocator);
    for (apps.items) |app| {
        var obj = std.json.ObjectWriter.init(allocator);
        try obj.put("id", app.id);
        try obj.put("name", app.name);
        try obj.put("version", app.version);
        try json_array.append(obj.end());
    }
    const json_text = json_array.end();
    defer allocator.free(json_text);

    try file.writeAll(json_text);
}

pub fn ams() !void {
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    const allocator = &gpa.allocator;

    const data_file = "apps.json";

    var apps = try loadApps(allocator, data_file);
    var id_counter: u32 = 1;
    for (apps.items) |app| {
        if (app.id >= id_counter) id_counter = app.id + 1;
    }

    var stdin = std.io.getStdIn().reader();
    var stdout = std.io.getStdOut().writer();

    while (true) {
        try stdout.print("\nSoftware Management System:\n1. Add App\n2. List Apps\n3. Remove App\n4. Exit\nSelect an option: ", .{});
        const line = try stdin.readLineAlloc(allocator, 100);
        defer allocator.free(line);

        const option = std.fmt.parseInt(u32, line, 10) catch 0;

        switch (option) {
            1 => {
                try stdout.print("Enter app name: ", .{});
                const name_line = try stdin.readLineAlloc(allocator, 100);
                defer allocator.free(name_line);

                try stdout.print("Enter app version: ", .{});
                const version_line = try stdin.readLineAlloc(allocator, 100);
                defer allocator.free(version_line);

                const app = App{
                    .id = id_counter,
                    .name = name_line,
                    .version = version_line,
                };
                id_counter += 1;

                try apps.append(app);
                try saveApps(allocator, data_file, &apps);
                try stdout.print("App added successfully!\n", .{});
            },
            2 => {
                if (apps.items.len == 0) {
                    try stdout.print("No applications found.\n", .{});
                } else {
                    for (apps.items) |app| {
                        try stdout.print("ID: {d}, Name: {s}, Version: {s}\n", .{ app.id, app.name, app.version });
                    }
                }
            },
            3 => {
                try stdout.print("Enter App ID to remove: ", .{});
                const id_line = try stdin.readLineAlloc(allocator, 10);
                defer allocator.free(id_line);

                const remove_id = std.fmt.parseInt(u32, id_line, 10) catch 0;
                var removed = false;
                var i: usize = 0;
                while (i < apps.items.len) : (i += 1) {
                    if (apps.items[i].id == remove_id) {
                        apps.items.swapRemove(i);
                        removed = true;
                        break;
                    }
                }
                if (removed) {
                    try saveApps(allocator, data_file, &apps);
                    try stdout.print("App removed successfully!\n", .{});
                } else {
                    try stdout.print("App ID not found.\n", .{});
                }
            },
            4 => break,
            else => try stdout.print("Invalid option, try again.\n", .{}),
        }
    }

    apps.deinit();
}
