const std = @import("std");
const kafka = @import("kafka.zig");

pub const KafkaProducer = struct {
    rk: *kafka.rd_kafka_t,
    topic: *kafka.rd_kafka_topic_t,

    pub fn init(
        allocator: std.mem.Allocator,
        brokers: []const u8,
        topic_name: []const u8,
    ) !KafkaProducer {
        var err_buf: [512]u8 = undefined;

        const conf = kafka.rd_kafka_conf_new();
        const rk = kafka.rd_kafka_new(
            .RD_KAFKA_PRODUCER,
            conf,
            &err_buf,
            err_buf.len,
        ) orelse return error.InitKafkaError;

        // add brokers
        var cname = try std.cstr.addNullByte(allocator, brokers);
        defer allocator.free(cname);

        if (kafka.rd_kafka_brokers_add(rk, cname.ptr) == 0)
            return error.NoBrokers;

        var topic_c = try std.cstr.addNullByte(allocator, topic_name);
        defer allocator.free(topic_c);

        const topic = kafka.rd_kafka_topic_new(rk, topic_c.ptr, null) orelse return error.TopicError;

        return .{
            .rk = rk,
            .topic = topic,
        };
    }

    pub fn publishAppCreated(self: *KafkaProducer, id: u32, name: []const u8, version: []const u8) !void {
        const json_str = try std.fmt.allocPrint(
            std.heap.page_allocator,
            "{{\"id\":{},\"name\":\"{}\",\"version\":\"{}\"}}",
            .{ id, name, version },
        );
        defer std.heap.page_allocator.free(json_str);

        const res = kafka.rd_kafka_produce(
            self.topic,
            kafka.RD_KAFKA_PARTITION_UA,
            kafka.RD_KAFKA_MSG_F_COPY,
            @ptrCast(*anyopaque, json_str.ptr),
            json_str.len,
            null,
            0,
        );

        if (res != 0) return error.ProduceFailed;

        // allow delivery reports to be processed
        _ = kafka.rd_kafka_poll(self.rk, 0);
    }
};
pub fn processAppCreated(event: AppCreatedEvent) !void {
    // heavy background work
    // e.g., update cache, notify other services
}
pub const AppCreatedEvent = struct {
    id: u32,
    name: []const u8,
    version: []const u8,
};
