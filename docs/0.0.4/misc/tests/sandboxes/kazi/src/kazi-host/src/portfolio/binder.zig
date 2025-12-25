// @copyright
// @brief
const std = @import("std");
const fs = std.fs;
const print = std.debug.print;

pub fn create_binder() void {
    print("creating binder");
}

pub fn add_project_by_id(project_id: u8) void {
    print("adding project by ID: {}", .{project_id});
}
