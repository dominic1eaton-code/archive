const std = @import("std");

pub const rd_kafka_conf_t = opaque {};
pub const rd_kafka_t = opaque {};
pub const rd_kafka_topic_t = opaque {};
pub const rd_kafka_type_t = enum(c_int) { RD_KAFKA_PRODUCER = 0 };

extern fn rd_kafka_new(
    type_: rd_kafka_type_t,
    conf: *rd_kafka_conf_t,
    errstr: [*:0]u8,
    errstr_size: usize,
) ?*rd_kafka_t;

extern fn rd_kafka_conf_new() *rd_kafka_conf_t;
extern fn rd_kafka_brokers_add(rk: *rd_kafka_t, brokers: [*:0]const u8) c_int;

extern fn rd_kafka_brokers_add(rk: *rd_kafka_t, brokers: [*:0]const u8) c_int;

extern fn rd_kafka_topic_new(
    rk: *rd_kafka_t,
    name: [*:0]const u8,
    conf: ?*rd_kafka_conf_t,
) ?*rd_kafka_topic_t;

extern fn rd_kafka_produce(
    topic: *rd_kafka_topic_t,
    partition: c_int,
    flags: c_int,
    payload: *anyopaque,
    len: usize,
    key: ?*anyopaque,
    keylen: usize,
) c_int;

extern fn rd_kafka_poll(rk: *rd_kafka_t, timeout_ms: c_int) c_int;

pub const RD_KAFKA_PARTITION_UA = -1;
pub const RD_KAFKA_MSG_F_COPY = 0x2;
