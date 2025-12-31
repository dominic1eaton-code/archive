// @license("MIT")
// @brief("")
// @author("qala development team")
// @copyright("2024 qala development team")
const std = @import("std");

pub const Project = struct {
    pub const Language = enum {
        Zig,
        // Future languages can be added here
    };

    name: []const u8,
    language: Language,
    repo_url: []const u8,
    default_branch: []const u8,
    package_manager: []const u8,

    pub fn create(
        name: []const u8,
        language: Project.Language,
        repo_url: []const u8,
        default_branch: []const u8,
        package_manager: []const u8,
    ) Project {
        return Project{
            .name = name,
            .language = language,
            .repo_url = repo_url,
            .default_branch = default_branch,
            .package_manager = package_manager,
        };
    }

    pub fn destroy(self: *Project) void {
        // No dynamic resources to free currently
    }

    pub fn getBuildScript(self: *const Project) []const u8 {
        switch (self.language) {
            .Zig => return "build.zig",
            // Future languages can have their build scripts defined here
        }
    }

    pub fn getTestScript(self: *const Project) []const u8 {
        switch (self.language) {
            .Zig => return "test.zig",
            // Future languages can have their test scripts defined here
        }
    }

    pub fn getDeployScript(self: *const Project) []const u8 {
        switch (self.language) {
            .Zig => return "deploy.zig",
            // Future languages can have their deploy scripts defined here
        }
    }

    pub fn getDocScript(self: *const Project) []const u8 {
        switch (self.language) {
            .Zig => return "doc.zig",
            // Future languages can have their doc scripts defined here
        }
    }

    pub fn getLintScript(self: *const Project) []const u8 {
        switch (self.language) {
            .Zig => return "lint.zig",
            // Future languages can have their lint scripts defined here
        }
    }

    pub fn getFormatScript(self: *const Project) []const u8 {
        switch (self.language) {
            .Zig => return "format.zig",
            // Future languages can have their format scripts defined here
        }
    }

    pub fn getCleanScript(self: *const Project) []const u8 {
        switch (self.language) {
            .Zig => return "clean.zig",
            // Future languages can have their clean scripts defined here
        }
    }

    pub fn getAnalyzeScript(self: *const Project) []const u8 {
        switch (self.language) {
            .Zig => return "analyze.zig",
            // Future languages can have their analyze scripts defined here
        }
    }

    pub fn getBenchmarkScript(self: *const Project) []const u8 {
        switch (self.language) {
            .Zig => return "benchmark.zig",
            // Future languages can have their benchmark scripts defined here
        }
    }

    pub fn getReleaseScript(self: *const Project) []const u8 {
        switch (self.language) {
            .Zig => return "release.zig",
            // Future languages can have their release scripts defined here
        }
    }

    pub fn getCiCdScript(self: *const Project) []const u8 {
        switch (self.language) {
            .Zig => return "cicd.zig",
            // Future languages can have their ci/cd scripts defined here
        }
    }

    pub fn getDependencyGraphScript(self: *const Project) []const u8 {
        switch (self.language) {
            .Zig => return "depgraph.zig",
            // Future languages can have their dependency graph scripts defined here
        }
    }

    pub fn getSchedulerScript(self: *const Project) []const u8 {
        switch (self.language) {
            .Zig => return "scheduler.zig",
            // Future languages can have their scheduler scripts defined here
        }
    }

    pub fn getAttestationScript(self: *const Project) []const u8 {
        switch (self.language) {
            .Zig => return "attestation.zig",
            // Future languages can have their attestation scripts defined here
        }
    }

    pub fn getAdministrationScript(self: *const Project) []const u8 {
        switch (self.language) {
            .Zig => return "admin.zig",
            // Future languages can have their administration scripts defined here
        }
    }

    pub fn getManagementScript(self: *const Project) []const u8 {
        switch (self.language) {
            .Zig => return "management.zig",
            // Future languages can have their management scripts defined here
        }
    }

    pub fn getSandboxScript(self: *const Project) []const u8 {
        switch (self.language) {
            .Zig => return "sandbox.zig",
            // Future languages can have their sandbox scripts defined here
        }
    }

    pub fn getBuildDependencyScript(self: *const Project) []const u8 {
        switch (self.language) {
            .Zig => return "build_dependency.zig",
            // Future languages can have their build dependency scripts defined here
        }
    }

    pub fn getGraphManagementScript(self: *const Project) []const u8 {
        switch (self.language) {
            .Zig => return "graph_management.zig",
            // Future languages can have their graph management scripts defined here
        }
    }

    pub fn getPipelineManagementScript(self: *const Project) []const u8 {
        switch (self.language) {
            .Zig => return "pipeline_management.zig",
            // Future languages can have their pipeline management scripts defined here
        }
    }

    pub fn getSchedulingScript(self: *const Project) []const u8 {
        switch (self.language) {
            .Zig => return "scheduling.zig",
            // Future languages can have their scheduling scripts defined here
        }
    }
};
