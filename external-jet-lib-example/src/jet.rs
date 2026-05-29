use std::io::Write;

use simplicityhl::{
    jet::{JetHL, SourceJetClassification, TargetJetClassification},
    simplicity::{
        decode::Error,
        decode_bits,
        jet::{type_name::TypeName, Jet},
        BitIter, BitWriter, Cmr, Cost, Error as SimplicityError,
    },
};

pub struct ExternalJet {
    pub index: u64,
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub enum HappyJet {
    Verify,
}

impl HappyJet {
    pub fn index(&self) -> u64 {
        match self {
            HappyJet::Verify => 0,
        }
    }

    pub fn from_index(index: u64) -> Option<Self> {
        match index {
            0 => Some(HappyJet::Verify),
            _ => None,
        }
    }
}

impl Jet for HappyJet {
    fn cmr(&self) -> Cmr {
        let bytes = match self {
            HappyJet::Verify => [
                0xcd, 0xca, 0x2a, 0x05, 0xe5, 0x2c, 0xef, 0xa5, 0x9d, 0xc7, 0xa5, 0xb0, 0xda, 0xe2,
                0x20, 0x98, 0xfb, 0x89, 0x6e, 0x39, 0x13, 0xbf, 0xdd, 0x44, 0x6b, 0x59, 0x4e, 0x1f,
                0x92, 0x50, 0x78, 0x3e,
            ],
        };
        Cmr::from_byte_array(bytes)
    }

    fn source_ty(&self) -> TypeName {
        let name: &'static [u8] = match self {
            HappyJet::Verify => b"2",
        };

        TypeName(name)
    }

    fn target_ty(&self) -> TypeName {
        let name: &'static [u8] = match self {
            HappyJet::Verify => b"1",
        };

        TypeName(name)
    }

    fn encode(&self, w: &mut BitWriter<&mut dyn Write>) -> std::io::Result<usize> {
        let (n, len) = match self {
            HappyJet::Verify => (0, 1),
        };

        w.write_bits_be(n, len)
    }

    fn decode<I: Iterator<Item = u8>>(bits: &mut BitIter<I>) -> Result<Self, Error>
    where
        Self: Sized,
    {
        decode_bits!(bits, {
            0 => {HappyJet::Verify},
            1 => {}
        })
    }

    fn cost(&self) -> Cost {
        match self {
            HappyJet::Verify => Cost::from_milliweight(44),
        }
    }

    fn parse(s: &str) -> Result<Self, SimplicityError>
    where
        Self: Sized,
    {
        match s {
            "verify" => Ok(HappyJet::Verify),
            x => Err(SimplicityError::InvalidJetName(x.to_owned())),
        }
    }
}

impl std::fmt::Display for HappyJet {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            HappyJet::Verify => write!(f, "verify"),
        }
    }
}

impl JetHL for HappyJet {
    fn source_jet_classification(&self) -> SourceJetClassification {
        match self {
            HappyJet::Verify => SourceJetClassification::Custom(vec![simplicityhl::jet::bool()]),
        }
    }

    fn target_jet_classification(&self) -> TargetJetClassification {
        match self {
            HappyJet::Verify => TargetJetClassification::Unary,
        }
    }

    fn is_disabled(&self) -> bool {
        false
    }

    fn clone_box(&self) -> Box<dyn JetHL> {
        Box::new(*self)
    }

    fn as_jet(&self) -> &dyn Jet {
        self
    }
}
