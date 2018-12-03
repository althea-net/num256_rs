extern crate failure;
#[macro_use]
extern crate num_derive;

extern crate num;
extern crate serde;

mod int256;
mod uint256;

pub use int256::Int256;
pub use uint256::Uint256;
