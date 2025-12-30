const std = @import("std");

pub const Config = struct {
    db_conn: []const u8,
    kafka_brokers: []const u8,
    kafka_topic: []const u8,

    pub fn load(allocator: std.mem.Allocator) !Config {
        const db_conn = try getEnvOr(allocator, "DB_CONN", "postgres://user:pass@localhost/appdb");
        const kafka_brokers = try getEnvOr(allocator, "KAFKA_BROKERS", "localhost:9092");
        const kafka_topic = try getEnvOr(allocator, "KAFKA_TOPIC", "app.created");

        return .{
            .db_conn = db_conn,
            .kafka_brokers = kafka_brokers,
            .kafka_topic = kafka_topic,
        };
    }
};

fn getEnvOr(allocator: std.mem.Allocator, key: []const u8, fallback: []const u8) ![]u8 {
    const env = std.process.getEnvVarOwned(allocator, key) catch return allocator.dupe(u8, fallback);
    return env;
}

const std = @import("std");

pub const Config = struct {
    listen_addr: []const u8,
    jwt_secret: []const u8,
    db_conn: []const u8,
    grpc_addr: []const u8,
    rate_limit_per_minute: u32,

    pub fn load(allocator: std.mem.Allocator) !Config {
        return .{
            .listen_addr = try getOr(allocator, "LISTEN_ADDR", "0.0.0.0:8080"),
            .jwt_secret = try getOr(allocator, "JWT_SECRET", "SUPERSECRET"),
            .db_conn = try getOr(allocator, "DB_CONN", "postgres://user:pass@localhost/userdb"),
            .grpc_addr = try getOr(allocator, "GRPC_ADDR", "127.0.0.1:50051"),
            .rate_limit_per_minute = try getIntOr("RATE_LIMIT", 60),
        };
    }
};

fn getOr(allocator: std.mem.Allocator, key: []const u8, fallback: []const u8) ![]u8 {
    return std.process.getEnvVarOwned(allocator, key) catch allocator.dupe(u8, fallback);
}

fn getIntOr(key: []const u8, fallback: u32) !u32 {
    return if (std.process.getEnvVarOwned(std.heap.page_allocator, key)) |s| {
        defer std.heap.page_allocator.free(s);
        std.fmt.parseInt(u32, s, 10)
    } else fallback;
}



pub const Config = struct {
    kafka_brokers: []const u8,
    kafka_topic: []const u8,
    db_conn: []const u8,
    concurrency: u32,

    pub fn load(allocator: std.mem.Allocator) !Config {
        const brokers = try getOr(allocator, "KAFKA_BROKERS", "localhost:9092");
        const topic = try getOr(allocator, "KAFKA_TOPIC", "app.created");
        const db_conn = try getOr(allocator, "DB_CONN", "postgres://user:pass@localhost/appdb");
        const concurrency = try getIntOr("WORKER_CONCURRENCY", 4);

        return .{
            .kafka_brokers = brokers,
            .kafka_topic = topic,
            .db_conn = db_conn,
            .concurrency = concurrency,
        };
    }
};

fn getOr(allocator: std.mem.Allocator, key: []const u8, fallback: []const u8) ![]u8 {
    return std.process.getEnvVarOwned(allocator, key) catch allocator.dupe(u8, fallback);
}

fn getIntOr(key: []const u8, fallback: u32) !u32 {
    return if (std.process.getEnvVarOwned(std.heap.page_allocator, key)) |s| {
        defer std.heap.page_allocator.free(s);
        std.fmt.parseInt(u32, s, 10)
    } else fallback;
}