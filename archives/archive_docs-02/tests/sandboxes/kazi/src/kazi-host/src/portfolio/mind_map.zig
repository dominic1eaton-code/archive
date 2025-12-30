//
//

pub fn add_node() void {}
pub fn remove_node() void {}
pub fn add_connector() void {}
pub fn remove_connector() void {}

const Data = struct {};

const Node = struct {
    img: u128,
    id: u128,
    name: u8,
    data: Data,
};

const Connector = struct {
    id: u128,
    color: u128,
};
