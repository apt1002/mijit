#[macro_use]
mod array_map;
pub use array_map::{ArrayMap, AsUsize};

mod iter;
pub use iter::{map_filter_max};

mod comma_separated;
pub use comma_separated::{CommaSeparated};

mod rotate;
pub use rotate::{rotate_left, rotate_right};

mod usage;
pub use usage::{Usage};

mod reverse_map;
pub use reverse_map::{reverse_map};

pub fn push_and_return_index<T>(vec: &mut Vec<T>, item: T) -> usize {
    let index = vec.len();
    vec.push(item);
    index
}