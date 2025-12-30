pub const KafkaProducer = struct {
    // init using rdkafka bindings
    pub fn publishAppCreated(self: *KafkaProducer, id: u32, name: []const u8, version: []const u8) !void {
        const msg = try std.fmt.allocPrint(std.heap.page_allocator, "{{\"id\":{},\"name\":\"{}\",\"version\":\"{}\"}}", .{ id, name, version });
        defer std.heap.page_allocator.free(msg);

        try self.producer.send("app.created", msg);
    }
};

pub fn processAppCreated(event: AppCreatedEvent) !void {
    // heavy background work
}
