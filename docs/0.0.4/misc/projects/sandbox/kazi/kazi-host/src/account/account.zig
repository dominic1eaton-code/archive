// @copyright
// @brief
const std = @import("std");
const bcrypt = std.crypto.pwhash.bcrypt;
const time = std.time;

pub const Account = struct {
    name: []u8,
    password: u128,
    pin: u8,
    token: u128,
    ssh_key: u128,
    settings: AccountSettings,

    // store data in database
    pub fn store_data() void {}

    pub fn create() void {}
    pub fn create_finance_account() void {}
    pub fn create_market_account() void {}
    pub fn create_community_account() void {}
    pub fn create_work_account() void {}
    pub fn create_portfolio() void {}
    pub fn create_workspace() void {}

    pub fn delete() void {}

    pub fn update() void {}

    pub fn read() void {}

    pub fn validate_name(self: *const Account) bool {
        // validate name input
        var valid: bool = true;
        if (std.mem.eql(u8, self.name, ""))
            valid = false;
        return valid;
    }

    pub fn validate_email() void {
        // validate email inpuT
    }

    pub fn validate_password() void {
        // password must be at least 10 characters
        // have at least one special character
        // have at least one number
        // have at least one uppercase letter
        // have at least one lowercase letter
    }

    pub fn verify_email() void {
        // send email verification code
    }

    pub fn generate_token(self: *const Account) void {
        return self.token;
    }

    pub fn authenticate_account() void {
        // authenticate user account
    }

    pub fn send_verification_code() void {
        // send verification pin code to email account
    }

    pub fn encrypt_password() void {
        // encrypt password
    }
};

pub const AccountSettings = struct {};
