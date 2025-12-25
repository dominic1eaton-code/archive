const std = @import("std");

pub fn sendSlackWebhook(url: []const u8, msg: []const u8) !void {
    var client = std.http.Client{};
    defer client.deinit();

    var req = try client.request(.POST, url, .{});
    try req.writer().print("{{\"text\":\"{s}\"}}", .{msg});
    _ = try req.finish();
}

pub fn sendEmailSMTP(server: []const u8, to: []const u8, body: []const u8) !void {
    // Simplified example (real SMTP needs auth)
    var client = try std.net.tcpConnectToHost(std.heap.page_allocator, server, 25);
    defer client.close();

    client.writer().print("MAIL FROM:<cd@system>\r\n", .{}) catch {};
    client.writer().print("RCPT TO:<{s}>\r\n", .{to}) catch {};
    client.writer().print("DATA\r\n{s}\r\n.\r\nQUIT\r\n", .{body}) catch {};
}
