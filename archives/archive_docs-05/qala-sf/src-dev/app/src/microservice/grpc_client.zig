const std = @import("std");
const grpc = @import("grpc_zig");
const gen = @import("gen/appmgmt.application_service_client.zig");

pub const GrpcClient = struct {
    client: gen.ApplicationServiceClient,

    pub fn init(allocator: std.mem.Allocator, addr: []const u8) !GrpcClient {
        var cli = try gen.ApplicationServiceClient.init(allocator, addr);
        return .{ .client = cli };
    }

    pub fn createApp(self: *GrpcClient, name: []const u8, version: []const u8) !gen.ApplicationResponse {
        return try self.client.CreateApplication(.{ .name = name, .version = version });
    }

    pub fn listApps(self: *GrpcClient) !gen.ListApplicationsResponse {
        return try self.client.ListApplications(.{});
    }
};
