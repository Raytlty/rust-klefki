/*!
Abstract Algebra Types
*/

#[macro_use]
mod macros;
pub mod field;
pub mod group;
mod registers;
mod traits;

pub use registers::{InCompleteField, RegisterField};
pub use traits::{Field, Group, MatMul, Xor};
