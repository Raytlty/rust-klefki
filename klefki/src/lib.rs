#![feature(trait_alias)]

/*! Klefki is a playground for researching elliptic curve group based cryptocoins, such as Bitcoin and Ethereum.
 All data types & structures are based on mathematical defination of abstract algebra.
*/

mod constrant;
pub mod crypto;
pub mod number;
#[macro_use]
pub mod algebra;
pub mod zkp;

#[macro_use]
extern crate lazy_static;
