
use macros::*;

include_simf!("./examples/source_simf/options2.simf");

pub const OPTION_SOURCE: &str = include_str!("source_simf/options.simf");

include_simf_source!(OPTION_SOURCE);

fn main( ){
    println!("{}", options2_hello1::options2_hello2);
    println!("{}", options2_hello1::options2_hello2);
}
