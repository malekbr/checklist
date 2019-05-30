extern crate pest;
#[macro_use]
extern crate pest_derive;
mod lib;

use lib::data_point;
fn main() {
    let result = std::fs::read_to_string("template-example.cltp").unwrap();
    data_point::Template::parse(&result).unwrap();
    println!("Hello, world!");
}
