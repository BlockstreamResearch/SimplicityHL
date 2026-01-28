use bincode::de::Decoder;
use bincode::enc::Encoder;
use bincode::error::{DecodeError, EncodeError};
use bincode::*;
use simplicityhl_macros::include_simf;
use std::ops::Deref;

include_simf!("examples/source_simf/options.simf");

fn main() {
    // println!("{}", options2::CONTRACT_SOURCE);
    // let x = options2::get_options_template_program();
}

// impl<Decodable> bincode::Decode<Decodable> for OptionsArguments {
//     fn decode<D: Decoder<Context = Decodable>>(decoder: &mut D) -> Result<Self, DecodeError> {
//         todo!()
//     }
// }
//
// impl bincode::Encode for OptionsArguments {
//     fn encode<E: Encoder>(&self, encoder: &mut E) -> Result<(), EncodeError> {
//         encoder.
//     }
// }
//
// impl<Decodable> bincode::Decode<Decodable> for OptionsWitness {
//     fn decode<D: Decoder<Context = Decodable>>(decoder: &mut D) -> Result<Self, DecodeError> {
//         todo!()
//     }
// }
//
// impl bincode::Encode for OptionsWitness {
//     fn encode<E: Encoder>(&self, encoder: &mut E) -> Result<(), EncodeError> {
//
//         todo!()
//     }
// }
