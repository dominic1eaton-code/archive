const std = @import("std");
const gen = @import("gen/application_service_server.zig");
const Db = @import("db.zig").Db;
const KafkaProducer = @import("kafka_producer.zig").KafkaProducer;

pub const ApplicationService = struct {
    db: *Db,
    producer: *KafkaProducer,

    pub fn CreateApplication(self: *ApplicationService, req: *gen.CreateApplicationRequest) !gen.ApplicationResponse {
        const id = try self.db.createApplication(req.name, req.version);

        try self.producer.publishAppCreated(id, req.name, req.version);

        return gen.ApplicationResponse{
            .app = .{ .id = id, .name = req.name, .version = req.version },
        };
    }

    pub fn GetApplication(self: *ApplicationService, req: *gen.GetApplicationRequest) !gen.ApplicationResponse {
        const rowOpt = try self.db.getApplication(req.id);
        if (rowOpt == null) return error.NotFound;

        const row = rowOpt.?;
        return gen.ApplicationResponse{
            .app = .{
                .id = try row.getInt(0),
                .name = try row.getString(1),
                .version = try row.getString(2),
            },
        };
    }

    pub fn ListApplications(self: *ApplicationService, _: *gen.ListApplicationsRequest) !gen.ListApplicationsResponse {
        var rows = try self.db.listApplications();
        defer rows.deinit();

        var list = std.ArrayList(gen.Application).init(std.heap.page_allocator);

        while (try rows.next()) |row| {
            try list.append(.{
                .id = try row.getInt(0),
                .name = try row.getString(1),
                .version = try row.getString(2),
            });
        }

        return gen.ListApplicationsResponse{ .apps = list.toOwnedSlice() };
    }
};
