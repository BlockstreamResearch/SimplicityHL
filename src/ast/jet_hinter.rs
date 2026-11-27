use simplicity::jet::{Bitcoin, Core, Elements, Jet};

use crate::jet::JetHL;

/// Object which produces a specific kind of jet.
///
/// All methods return a `dyn Jet` rather than the specific jet so that the trait itself
/// can be object-safe. However, implementors of this trait **must** ensure that
/// all methods return the same kind of jet to avoid panics.
///
/// Users may rely on this property for correctness of their code, though since this
/// is a safe trait, of course they may not rely on it for soundness.
pub trait JetHinter: std::fmt::Debug + Send + Sync {
    /// Attempts to parse a jet from a string.
    fn parse_jet(&self, name: &str) -> Option<Box<dyn JetHL>>;
    /// Constructs an instance of the `verify` jet.
    fn construct_verify(&self) -> Box<dyn JetHL>;
    /// Converts a runtime Simplicity jet back into this hinter's high-level jet.
    fn conjure(&self, jet: &dyn Jet) -> Option<Box<dyn JetHL>>;

    /// Clones the `JetHinter` into a boxed trait object.
    fn clone_box(&self) -> Box<dyn JetHinter>;

    // The methods below default to `None`, so an implementation written before
    // they were added, or one for a jet set without the SHA-256 context jets,
    // keeps compiling; `raw_hash` then reports that the jets are unavailable.
    //
    // TODO: These return `Option` because a jet set need not contain the SHA-256
    // context jets; an external jet library may define any jets it likes. Once
    // rust-simplicity requires every jet set to provide the essential jets, these
    // can become infallible like `construct_verify`. See
    // https://github.com/BlockstreamResearch/SimplicityHL/pull/423#issuecomment-5798922942

    /// Constructs an instance of the `sha_256_ctx_8_init` jet, if this jet set has it.
    fn construct_sha_256_ctx_8_init(&self) -> Option<Box<dyn JetHL>> {
        None
    }

    /// Constructs an instance of the `sha_256_ctx_8_add_1` jet, if this jet set has it.
    fn construct_sha_256_ctx_8_add_1(&self) -> Option<Box<dyn JetHL>> {
        None
    }

    /// Constructs an instance of the `sha_256_ctx_8_add_2` jet, if this jet set has it.
    fn construct_sha_256_ctx_8_add_2(&self) -> Option<Box<dyn JetHL>> {
        None
    }

    /// Constructs an instance of the `sha_256_ctx_8_add_4` jet, if this jet set has it.
    fn construct_sha_256_ctx_8_add_4(&self) -> Option<Box<dyn JetHL>> {
        None
    }

    /// Constructs an instance of the `sha_256_ctx_8_add_8` jet, if this jet set has it.
    fn construct_sha_256_ctx_8_add_8(&self) -> Option<Box<dyn JetHL>> {
        None
    }

    /// Constructs an instance of the `sha_256_ctx_8_add_16` jet, if this jet set has it.
    fn construct_sha_256_ctx_8_add_16(&self) -> Option<Box<dyn JetHL>> {
        None
    }

    /// Constructs an instance of the `sha_256_ctx_8_add_32` jet, if this jet set has it.
    fn construct_sha_256_ctx_8_add_32(&self) -> Option<Box<dyn JetHL>> {
        None
    }

    /// Constructs an instance of the `sha_256_ctx_8_finalize` jet, if this jet set has it.
    fn construct_sha_256_ctx_8_finalize(&self) -> Option<Box<dyn JetHL>> {
        None
    }
}

macro_rules! impl_jet_hinter {
    ($struct_name:ident, $jet_type:ident) => {
        #[derive(Clone, Debug, Default)]
        pub struct $struct_name;

        impl $struct_name {
            pub fn new() -> Self {
                Self
            }
        }

        impl JetHinter for $struct_name {
            fn parse_jet(&self, name: &str) -> Option<Box<dyn JetHL>> {
                $jet_type::parse(name)
                    .ok()
                    .map(|jet| -> Box<dyn JetHL> { Box::new(jet) })
            }

            fn construct_verify(&self) -> Box<dyn JetHL> {
                Box::new($jet_type::Verify)
            }

            fn conjure(&self, jet: &dyn Jet) -> Option<Box<dyn JetHL>> {
                jet.as_any()
                    .downcast_ref::<$jet_type>()
                    .map(|jet| Box::new(*jet) as Box<dyn JetHL>)
            }

            fn clone_box(&self) -> Box<dyn JetHinter> {
                Box::new(Self)
            }

            fn construct_sha_256_ctx_8_init(&self) -> Option<Box<dyn JetHL>> {
                Some(Box::new($jet_type::Sha256Ctx8Init))
            }
            fn construct_sha_256_ctx_8_add_1(&self) -> Option<Box<dyn JetHL>> {
                Some(Box::new($jet_type::Sha256Ctx8Add1))
            }
            fn construct_sha_256_ctx_8_add_2(&self) -> Option<Box<dyn JetHL>> {
                Some(Box::new($jet_type::Sha256Ctx8Add2))
            }
            fn construct_sha_256_ctx_8_add_4(&self) -> Option<Box<dyn JetHL>> {
                Some(Box::new($jet_type::Sha256Ctx8Add4))
            }
            fn construct_sha_256_ctx_8_add_8(&self) -> Option<Box<dyn JetHL>> {
                Some(Box::new($jet_type::Sha256Ctx8Add8))
            }
            fn construct_sha_256_ctx_8_add_16(&self) -> Option<Box<dyn JetHL>> {
                Some(Box::new($jet_type::Sha256Ctx8Add16))
            }
            fn construct_sha_256_ctx_8_add_32(&self) -> Option<Box<dyn JetHL>> {
                Some(Box::new($jet_type::Sha256Ctx8Add32))
            }
            fn construct_sha_256_ctx_8_finalize(&self) -> Option<Box<dyn JetHL>> {
                Some(Box::new($jet_type::Sha256Ctx8Finalize))
            }
        }
    };
}

impl_jet_hinter!(ElementsJetHinter, Elements);
impl_jet_hinter!(BitcoinJetHinter, Bitcoin);
impl_jet_hinter!(CoreJetHinter, Core);
