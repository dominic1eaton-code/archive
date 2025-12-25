const std = @import("std");
const Jwt = @import("jwt.zig").Jwt;
const Users = @import("users.zig").Users;
const RL = @import("rate_limit.zig").RateLimiter;
const GC = @import("grpc_client.zig").GrpcClient;

pub fn handle(
    req: *std.http.Server.Request,
    res: *std.http.Server.Response,
    jwt: *Jwt,
    users: *Users,
    rl: *RL,
    gc: *GC,
) !void {
    if (!rl.allow(req.client_ip)) {
        res.status = .too_many_requests;
        return res.send("Rate limit exceeded");
    }

    switch (req.method) {
        .POST => {
            if (std.mem.eql(u8, req.path, "/register"))
                return register(req, res, users, jwt);
            if (std.mem.eql(u8, req.path, "/login"))
                return login(req, res, users, jwt);
            if (std.mem.eql(u8, req.path, "/apps"))
                return createApp(req, res, jwt, gc);
        },
        .GET => {
            if (std.mem.eql(u8, req.path, "/apps"))
                return listApps(req, res, jwt, gc);
        },
        else => {},
    }

    res.status = .not_found;
    try res.send("Not found");
}

fn register(req: *..., res: *..., users: *Users, jwt: *Jwt) !void {
    const body = req.body;
    const email = try parseJsonField(body, "email");
    const password = try parseJsonField(body, "password");

    const id = try users.register(email, password);
    const tokens = try jwt.createTokens(id, std.heap.page_allocator);

    return sendTokens(res, tokens);
}

fn login(...) {
    // identical flow
}

fn createApp(req: *..., res: *..., jwt: *Jwt, gc: *GC) !void {
    const token = req.headers.get("Authorization") orelse return unauthorized(res);
    const uid = try jwt.verify(token["Bearer ".len..], std.heap.page_allocator);

    const name = try parseJsonField(req.body, "name");
    const ver = try parseJsonField(req.body, "version");

    const result = try gc.createApp(name, ver);
    return res.json(result);
}

fn listApps(...) {
    const token = req.headers.get("Authorization") orelse return unauthorized(res);
    _ = try jwt.verify(token["Bearer ".len..], std.heap.page_allocator);

    const result = try gc.listApps();
    return res.json(result);
}

fn sendTokens(res: *std.http.Server.Response, tokens: JwtPair) !void {
    const json_str = try std.fmt.allocPrint(
        std.heap.page_allocator,
        "{{\"access\":\"{}\",\"refresh\":\"{}\"}}",
        .{ tokens.access, tokens.refresh },
    );
    defer std.heap.page_allocator.free(json_str);

    res.status = .ok;
    res.headers.set("Content-Type", "application/json");
    return res.send(json_str);
}

fn unauthorized(res: *std.http.Server.Response) !void {
    res.status = .unauthorized;
    return res.send("Unauthorized");
}

fn parseJsonField(body: []const u8, field: []const u8) ![]const u8 {
    const json = try std.json.parse(std.heap.page_allocator, body);
    const value = json.object.get(field) orelse return error.MissingField;
    return value.string;
}
