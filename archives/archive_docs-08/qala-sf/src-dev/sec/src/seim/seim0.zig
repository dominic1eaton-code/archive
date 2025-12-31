const std = @import("std");
const hash = std.crypto.hash;

pub const LogEvent = struct {
    timestamp: []const u8,
    source: []const u8,
    event_type: []const u8,
    message: []const u8,
};

var prev_hash: [32]u8 = undefined;

fn logEvent(event: LogEvent) !void {
    const json_str = try std.fmt.allocPrint(std.heap.page_allocator, "{{\"timestamp\": \"{s}\", \"source\": \"{s}\", \"event_type\": \"{s}\", \"message\": \"{s}\"}}", .{ event.timestamp, event.source, event.event_type, event.message });
    defer std.heap.page_allocator.free(json_str);

    // Compute chain hash
    var buf = try std.heap.page_allocator.alloc(u8, json_str.len + prev_hash.len);
    defer std.heap.page_allocator.free(buf);
    std.mem.copy(u8, buf[0..json_str.len], json_str);
    std.mem.copy(u8, buf[json_str.len..], prev_hash[0..]);
    const new_hash = hash.sha256(buf);

    // Append to log file
    const file = try std.fs.cwd().openFileAppend("events.log", .{});
    defer file.close();
    try file.writeAll(json_str);
    try file.writeAll(" || ");
    try file.writeAll(std.fmt.bytesToHex(new_hash, .lower));
    try file.writeAll("\n");

    prev_hash = new_hash;
}

fn saveEvent(event: LogEvent) !void {
    const file = try std.fs.cwd().openFileAppend("events.json", .{});
    defer file.close();
    const line = try std.fmt.allocPrint(std.heap.page_allocator, "{{\"timestamp\":\"{s}\",\"source\":\"{s}\",\"event_type\":\"{s}\",\"message\":\"{s}\"}}\n", .{ event.timestamp, event.source, event.event_type, event.message });
    defer std.heap.page_allocator.free(line);
    try file.writeAll(line);
}

fn analyzeEvent(event: LogEvent) void {
    if (std.mem.eql(u8, event.event_type, "login_failed")) {
        // increment counter, check window, raise alert
        std.debug.print("ALERT: Failed login detected from {s}\n", .{event.source});
    }
}

pub fn main() !void {
    var allocator = std.heap.page_allocator;

    prev_hash = [_]u8{0} ** 32;

    while (true) {
        const input = try prompt(allocator, "Enter log (source,event_type,message) or 'exit'");
        defer allocator.free(input);

        if (std.mem.eql(u8, input, "exit")) break;

        // Simple CSV parse
        const parts = std.mem.split(input, ",", false);
        if (parts.len != 3) continue;

        const event = LogEvent{
            .timestamp = "2025-11-27T12:00:00Z",
            .source = parts[0],
            .event_type = parts[1],
            .message = parts[2],
        };

        try logEvent(event);
        try saveEvent(event);
        analyzeEvent(event);
    }
}
