/*!
Abstract Algebra Types
*/

#[macro_use]
mod macros;
pub mod field;
pub mod group;
mod registers;
pub mod traits;

pub use registers::{InCompleteField, RegisterField};
