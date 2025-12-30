const std = @import("std");

pub const PackageRecord = struct {
    name: []const u8,
    version: []const u8,
    path: []const u8,
};

pub fn loadDB(allocator: *std.mem.Allocator, path: []const u8) !std.json.Value {
    const file = try std.fs.cwd().openFile(path, .{});
    defer file.close();

    const contents = try file.readToEndAlloc(allocator, 1024);
    defer allocator.free(contents);

    const json = try std.json.parse(allocator, contents);
    return json;
}

pub fn saveDB(allocator: *std.mem.Allocator, path: []const u8, json: std.json.Value) !void {
    const file = try std.fs.cwd().createFile(path, .{});
    defer file.close();

    const writer = file.writer();
    try json.print(writer, .{});
}

pub fn addPackage(allocator: *std.mem.Allocator, path: []const u8, pkg: PackageRecord) !void {
    var db_json = try loadDB(allocator, path);
    var pkg_array = db_json.Array orelse &[_]std.json.Value{};

    var new_pkg = std.json.Object.init(allocator);
    try new_pkg.put("name", pkg.name);
    try new_pkg.put("version", pkg.version);
    try new_pkg.put("path", pkg.path);

    try pkg_array.append(std.json.Value.fromObject(new_pkg));
    try saveDB(allocator, path, std.json.Value.fromArray(pkg_array));
}
