// siem.zig
const std = @import("std");
const hash = std.crypto.hash;
const json = std.json;

const EVENT_FILE = "events.json";
const EVENT_HASH_FILE = "events.hash";
const LOG_FILE = "events.log";

const Allocator = std.mem.Allocator;

pub const LogEvent = struct {
    timestamp: []const u8,
    source: []const u8,
    event_type: []const u8,
    message: []const u8,
};

// --- Globals ---
var prev_log_hash: [32]u8 = undefined;

// --- Utilities ---
fn prompt(allocator: *Allocator, msg: []const u8) ![]u8 {
    try std.debug.print("{s}: ", .{msg});
    var line = try std.io.getStdIn().readLineAlloc(allocator, 1024);
    if (line.len > 0 and line[line.len-1] == '\n') {
        _ = line[0..line.len-1];
    }
    return line;
}

fn currentTimestamp(allocator: *Allocator) ![]u8 {
    const ts = try std.time.now().format(.RFC3339, std.time.Zone.utc, allocator);
    return ts;
}

// --- File integrity ---
fn computeFileHash(path: []const u8, allocator: *Allocator) ![32]u8 {
    if (!std.fs.cwd().exists(path)) return [_]u8{0} ** 32;
    const file = try std.fs.cwd().openFile(path, .{});
    defer file.close();
    const data = try file.readToEndAlloc(allocator, 8192);
    defer allocator.free(data);
    return hash.sha256(data);
}

fn saveFileHash(path: []const u8, digest: [32]u8) !void {
    const file = try std.fs.cwd().createFile(path, .{});
    defer file.close();
    try file.writeAll(std.fmt.bytesToHex(digest, .lower));
}

fn verifyFileIntegrity(path: []const u8, hash_path: []const u8, allocator: *Allocator) !bool {
    if (!std.fs.cwd().exists(path) or !std.fs.cwd().exists(hash_path)) return true;
    const actual = try computeFileHash(path, allocator);
    const hash_file = try std.fs.cwd().openFile(hash_path, .{});
    defer hash_file.close();
    const data = try hash_file.readToEndAlloc(allocator, 1024);
    defer allocator.free(data);
    var expected: [32]u8 = undefined;
    _ = try std.fmt.hexToBytes(expected[0..], std.mem.trim(data, " \r\n"), .lower);
    return std.mem.eql(u8, actual[0..], expected[0..]);
}

// --- Chain-hash log ---
fn initLog() !void {
    if (!std.fs.cwd().exists(LOG_FILE)) {
        for (prev_log_hash.*) |*b| { b.* = 0; }
        return;
    }
    const file = try std.fs.cwd().openFile(LOG_FILE, .{});
    defer file.close();
    const data = try file.readToEndAlloc(std.heap.page_allocator, 8192);
    defer std.heap.page_allocator.free(data);
    const lines = std.mem.split(data, "\n", false);
    if (lines.len == 0) {
        for (prev_log_hash.*) |*b| { b.* = 0; }
        return;
    }
    const last = lines[lines.len-1];
    const parts = std.mem.split(last, "||", false);
    if (parts.len != 2) {
        for (prev_log_hash.*) |*b| { b.* = 0; }
        return;
    }
    const hex = std.mem.trim(parts[1], " \r\n");
    _ = try std.fmt.hexToBytes(prev_log_hash[0..], hex, .lower);
}

fn logAction(action: []const u8) !void {
    const ts = try currentTimestamp(std.heap.page_allocator);
    defer std.heap.page_allocator.free(ts);

    const entry = try std.fmt.allocPrint(std.heap.page_allocator, "{s} - {s}", .{ts, action});
    defer std.heap.page_allocator.free(entry);

    const buf_len = entry.len + prev_log_hash.len;
    var buf = try std.heap.page_allocator.alloc(u8, buf_len);
    defer std.heap.page_allocator.free(buf);
    std.mem.copy(u8, buf[0..entry.len], entry);
    std.mem.copy(u8, buf[entry.len..], prev_log_hash[0..]);

    const new_hash = hash.sha256(buf);

    const file = try std.fs.cwd().openFileAppend(LOG_FILE, .{});
    defer file.close();
    try file.writeAll(entry);
    try file.writeAll(" || ");
    try file.writeAll(std.fmt.bytesToHex(new_hash, .lower));
    try file.writeAll("\n");

    prev_log_hash = new_hash;
}

// --- Event storage ---
fn saveEvent(allocator: *Allocator, e: LogEvent) !void {
    const file = try std.fs.cwd().openFileAppend(EVENT_FILE, .{});
    defer file.close();
    const line = try std.fmt.allocPrint(allocator,
        "{{\"timestamp\":\"{s}\",\"source\":\"{s}\",\"event_type\":\"{s}\",\"message\":\"{s}\"}}\n",
        .{e.timestamp, e.source, e.event_type, e.message});
    defer allocator.free(line);
    try file.writeAll(line);

    const digest = try computeFileHash(EVENT_FILE, allocator);
    try saveFileHash(EVENT_HASH_FILE, digest);
}

// --- Event analysis ---
fn analyzeEvent(e: LogEvent) void {
    if (std.mem.eql(u8, e.event_type, "login_failed")) {
        std.debug.print("ALERT: Failed login detected from {s}\n", .{e.source});
    }
}

// --- Load events from JSON ---
fn loadEvents(allocator: *Allocator) ![]LogEvent {
    if (!std.fs.cwd().exists(EVENT_FILE)) return &[_]LogEvent{};
    const file = try std.fs.cwd().openFile(EVENT_FILE, .{});
    defer file.close();
    const data = try file.readToEndAlloc(allocator, 8192);
    defer allocator.free(data);

    var parser = json.Parser.init(data);
    const root = try parser.parseRoot();
    if (root.getType() != .Array) return &[_]LogEvent{};
    const arr = root.Array() orelse return &[_]LogEvent{};

    var events = try allocator.alloc(LogEvent, arr.len);
    for (arr.items()) |item, i| {
        const obj = item.Object() orelse continue;
        const ts = obj.get("timestamp").String() orelse "";
        const src = obj.get("source").String() orelse "";
        const etype = obj.get("event_type").String() orelse "";
        const msg = obj.get("message").String() orelse "";
        events[i] = LogEvent{ .timestamp=ts, .source=src, .event_type=etype, .message=msg };
    }
    return events;
}

// --- CLI loop ---
pub fn main() !void {
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    const allocator = &gpa.allocator;

    try initLog();

    if (!verifyFileIntegrity(EVENT_FILE, EVENT_HASH_FILE, allocator)) {
        std.debug.print("Warning: Event file integrity check failed!\n", .{});
    }

    var events = try loadEvents(allocator);

    while (true) {
        std.debug.print(
            "\nCommands: add, list, exit\n> ", .{});
        const cmd_raw = try std.io.getStdIn().readLineAlloc(allocator, 64);
        defer allocator.free(cmd_raw);
        const cmd = std.mem.trim(cmd_raw, " \r\n");

        if (std.mem.eql(u8, cmd, "exit")) break;

        if (std.mem.eql(u8, cmd, "add")) {
            const src = try prompt(allocator, "Source");
            const etype = try prompt(allocator, "Event Type");
            const msg = try prompt(allocator, "Message");
            const ts = try currentTimestamp(allocator);
            const e = LogEvent{ .timestamp=ts, .source=src, .event_type=etype, .message=msg };
            try saveEvent(allocator, e);
            try logAction("Added event: " ++ etype ++ " from " ++ src);
            analyzeEvent(e);
            events = try allocator.realloc(events, events.len + 1);
            events[events.len-1] = e;
        } else if (std.mem.eql(u8, cmd, "list")) {
            for (events) |ev| {
                std.debug.print("[{s}] {s}: {s}\n", .{ev.timestamp, ev.source, ev.message});
            }
        } else {
            std.debug.print("Unknown command: {s}\n", .{cmd});
        }
    }
}
