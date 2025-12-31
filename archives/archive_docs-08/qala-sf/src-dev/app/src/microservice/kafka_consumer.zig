const std = @import("std");
const kafka = @import("kafka.zig");

pub const KafkaConsumer = struct {
    rk: *kafka.rd_kafka_t,
    topic: *kafka.rd_kafka_topic_t,

    pub fn init(allocator: std.mem.Allocator, brokers: []const u8, topic_name: []const u8) !KafkaConsumer {
        var err_buf: [512]u8 = undefined;

        const conf = kafka.rd_kafka_conf_new();
        const rk = kafka.rd_kafka_new(.RD_KAFKA_CONSUMER, conf, &err_buf, err_buf.len) orelse return error.InitKafkaError;

        var cname = try std.cstr.addNullByte(allocator, brokers);
        defer allocator.free(cname);
        if (kafka.rd_kafka_brokers_add(rk, cname.ptr) == 0) return error.NoBrokers;

        var topic_c = try std.cstr.addNullByte(allocator, topic_name);
        defer allocator.free(topic_c);

        const topic = kafka.rd_kafka_topic_new(rk, topic_c.ptr, null) orelse return error.TopicError;

        return .{ .rk = rk, .topic = topic };
    }

    pub fn poll(self: *KafkaConsumer, timeout_ms: i32) ?[]const u8 {
        const msg = kafka.rd_kafka_consume(self.topic, kafka.RD_KAFKA_PARTITION_UA, timeout_ms);
        if (msg == null) return null;
        return msg.payload[0..msg.len];
    }
};
