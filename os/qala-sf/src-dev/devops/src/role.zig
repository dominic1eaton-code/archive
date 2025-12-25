pub fn requireRole(user_role: Role, allowed: []Role) bool {
    for (allowed) |r| if (r == user_role) return true;
    return false;
}

pub const Role = enum {
    Admin,
    Developer,
    Viewer,
};

pub const allRoles = [_]Role{ .Admin, .Developer, .Viewer };
pub fn roleToString(role: Role) []const u8 {
    return switch (role) {
        .Admin => "Admin",
        .Developer => "Developer",
        .Viewer => "Viewer",
    };
}

pub fn stringToRole(s: []const u8) ?Role {
    return switch (s) {
        "Admin" => Role.Admin,
        "Developer" => Role.Developer,
        "Viewer" => Role.Viewer,
        else => null,
    };
}

pub fn isValidRole(s: []const u8) bool {
    return switch (s) {
        "Admin", "Developer", "Viewer" => true,
        else => false,
    };
}

pub fn getAllRoleStrings() []const []const u8 {
    return [_][]const u8{
        "Admin",
        "Developer",
        "Viewer",
    };
}

pub fn handleRest(self: *Controller, req: *Request, res: *Response) !void {
    const jwt = req.header("Authorization") orelse return res.unauthorized();
    const role = try verifyJWT(jwt, self.config.jwt_secret) orelse return res.unauthorized();

    if (req.is("POST", "/api/pipelines/:name/run")) {
        if (!requireRole(role, .{ .admin, .developer })) return res.forbidden();
        try self.apiRunPipeline(name, res);
        return;
    }

    if (req.is("DELETE", "/api/agents/:id")) {
        if (!requireRole(role, .{.admin})) return res.forbidden();
        try self.apiDisconnectAgent(agent_id, res);
        return;
    }

    // other endpoints
}
