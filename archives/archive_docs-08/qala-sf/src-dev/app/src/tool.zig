// Installing a Tool Using a Plugin
pub fn installFromPlugin(env: *EnvManager, allocator: *std.mem.Allocator, plugin_name: []const u8, version: []const u8) !void {
    const p = try loadPlugin(allocator, plugin_name);

    // Replace {version} in download URL
    const url = try std.fmt.allocPrint(allocator, p.download_url_template, .{version});

    try env.install(plugin_name, version, url);

    // Shim creation
    const bin_path = try std.fmt.allocPrint(allocator, "{s}/{s}/{s}/bin/{s}", .{ ".envmgr/cache", plugin_name, version, plugin_name });
    try shim.createShim(allocator, plugin_name, bin_path);
}
fn fetchPluginVersions(allocator: *std.mem.Allocator, p: plugin.Plugin) ![]const u8 {
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    defer gpa.deinit();
    const ga = &gpa.allocator;

    const http_client = std.http.Client.init(ga);
    defer http_client.deinit();

    const response = try http_client.get(p.versions_url, .{});
    defer response.close();

    const body = try response.bodyReader().readToEndAlloc(allocator, 8192);
    defer allocator.free(body);

    var parser = std.json.Parser.init(body);
    const root = try parser.parseRoot();
    const arr = root.Array();

    var versions = std.ArrayList([]const u8).init(allocator);
    defer versions.deinit();

    for (arr.items) |item| {
        const ver = item.String();
        _ = try versions.append(ver);
    }

    return versions.toOwnedSlice();
}
fn resolveVersion(requested: []const u8, available: []const []const u8) ![]const u8 {
    if (requested == "latest") {
        if (available.len == 0) return error.VersionNotFound;
        return available[0];
    } else {
        for (available) |ver| {
            if (std.mem.eql(u8, ver, requested)) {
                return ver;
            }
        }
        return error.NoMatchingVersion;
    }
}

pub fn loadPlugin(allocator: *std.mem.Allocator, name: []const u8) !plugin.Plugin {
    return try plugin.getPlugin(allocator, name);
}

pub fn installTool(env: *EnvManager, allocator: *std.mem.Allocator, plugin_name: []const u8, requested_version: []const u8) !void {
    const plugin = try loadPlugin(allocator, plugin_name);
    const available_versions = try fetchPluginVersions(allocator, plugin);

    const version = try resolveVersion(requested_version, available_versions);

    // Build download URL
    const url = try std.fmt.allocPrint(allocator, plugin.download_url_template, .{version});
    try env.install(plugin_name, version, url);

    // Create shim automatically
    const bin_path = try std.fmt.allocPrint(allocator, "{s}/{s}/{s}/bin/{s}", .{ ".envmgr/cache", plugin_name, version, plugin_name });
    try shim.createShim(allocator, plugin_name, bin_path);

    std.debug.print("Installed {s} {s} from plugin {s}\n", .{ plugin_name, version, plugin_name });

    // Update lockfile
    var lock = try Config.loadLockfile(allocator, ".envmgr.lock") orelse std.StringHashMap([]const u8).init(allocator);
    _ = try lock.put(plugin_name, version);
    try Config.saveLockfile(allocator, ".envmgr.lock", lock);
}
