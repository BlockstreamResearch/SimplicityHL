use simplicityhl::ast::{CoreJetHinter, ElementsJetHinter, JetHinter, SourceJetHinter};
use simplicityhl::parse::CompilationTarget;
use simplicityhl::{Arguments, CompiledProgram, TemplateAst, UnstableFeature, UnstableFeatures};

const ELEMENTS: &str = "fn main() { assert!(jet::eq_32(1, 1)); }";

fn compile(
    source: &str,
    features: &UnstableFeatures,
    hinter: Box<dyn JetHinter>,
) -> Result<CompiledProgram, String> {
    CompiledProgram::new_with_unstable(source, features, Arguments::default(), false, hinter)
}

#[test]
fn undeclared_and_explicit_elements_keep_the_existing_commitment() {
    let old = compile(
        ELEMENTS,
        &UnstableFeatures::none(),
        Box::new(ElementsJetHinter::new()),
    )
    .unwrap();
    for source in [ELEMENTS.to_owned(), format!("target elements; {ELEMENTS}")] {
        let new = compile(
            &source,
            &UnstableFeatures::none(),
            Box::new(SourceJetHinter::new()),
        )
        .unwrap();
        assert_eq!(old.commit().cmr(), new.commit().cmr());
        assert_eq!(new.compilation_target(), Some(CompilationTarget::Elements));
    }
}

#[test]
fn target_remains_a_contextual_keyword() {
    compile("fn target() -> u32 { 1 } fn main() { let target: u32 = target(); assert!(jet::eq_32(target, 1)); }",
        &UnstableFeatures::none(), Box::new(SourceJetHinter::new())).unwrap();
}

#[test]
fn invalid_target_declarations_are_diagnosed() {
    for (source, expected) in [
        (
            "target elements; target elements; fn main() {}",
            "duplicate target",
        ),
        (
            "target elements; target bitcoin; fn main() {}",
            "duplicate target",
        ),
        ("target signet; fn main() {}", "unknown compilation target"),
        ("mod inner { target elements; } fn main() {}", "top level"),
    ] {
        let err = compile(
            source,
            &UnstableFeatures::all(),
            Box::new(SourceJetHinter::new()),
        )
        .unwrap_err();
        assert!(err.contains(expected), "{err}");
    }
}

#[test]
fn explicit_hinters_cannot_be_silently_replaced_by_source() {
    let err = compile(
        "target elements; fn main() {}",
        &UnstableFeatures::none(),
        Box::new(CoreJetHinter::new()),
    )
    .unwrap_err();
    assert!(err.contains("conflicts"), "{err}");
    let err = compile(
        "target bitcoin; fn main() {}",
        &UnstableFeatures::all(),
        Box::new(ElementsJetHinter::new()),
    )
    .unwrap_err();
    assert!(err.contains("conflicts"), "{err}");
}

#[test]
fn bitcoin_requires_the_runtime_feature() {
    let err = compile(
        "target bitcoin; fn main() {}",
        &UnstableFeatures::none(),
        Box::new(SourceJetHinter::new()),
    )
    .unwrap_err();
    assert!(
        err.contains("bitcoin") && err.contains("-Z bitcoin"),
        "{err}"
    );
}

#[test]
#[cfg(not(feature = "unstable-bitcoin"))]
fn bitcoin_requires_the_cargo_feature_too() {
    let err = compile(
        "target bitcoin; fn main() {}",
        &UnstableFeatures::new([UnstableFeature::Bitcoin]),
        Box::new(SourceJetHinter::new()),
    )
    .unwrap_err();
    assert!(err.contains("unstable-bitcoin Cargo feature"), "{err}");
}

#[test]
fn entry_target_survives_import_flattening_and_dependencies_cannot_declare_it() {
    use simplicityhl::resolution::DependencyMapBuilder;
    use simplicityhl::source::{CanonPath, CanonSourceFile};
    use std::path::Path;
    use std::sync::Arc;
    let targets = if cfg!(feature = "unstable-bitcoin") {
        vec!["elements", "bitcoin"]
    } else {
        vec!["elements"]
    };
    for target in targets {
        let root =
            Path::new(env!("CARGO_TARGET_TMPDIR")).join(format!("target-flattening-{target}"));
        std::fs::create_dir_all(&root).unwrap();
        let source = format!("target {target}; use crate::helper::value; fn main() {{ assert!(jet::eq_32(value(), 1)); }}");
        let main = root.join("main.simf");
        let helper = root.join("helper.simf");
        std::fs::write(&main, &source).unwrap();
        std::fs::write(&helper, "pub fn value() -> u32 { 1 }").unwrap();
        let deps = DependencyMapBuilder::new()
            .build(CanonPath::canonicalize(&root).unwrap())
            .unwrap();
        let canon =
            CanonSourceFile::new(CanonPath::canonicalize(&main).unwrap(), Arc::from(source));
        let features = UnstableFeatures::new([UnstableFeature::Imports, UnstableFeature::Bitcoin]);
        let original = TemplateAst::new_with_dep(
            canon.clone(),
            &deps,
            &features,
            Box::new(SourceJetHinter::new()),
        )
        .unwrap()
        .instantiate(Arguments::default(), false)
        .unwrap();
        let flat = TemplateAst::flatten(canon.clone(), &deps, &features).unwrap();
        let declaration = format!("target {target};");
        assert!(flat.starts_with(&declaration), "{flat}");
        assert_eq!(flat.matches(&declaration).count(), 1);
        let reparsed = compile(&flat, &features, Box::new(SourceJetHinter::new())).unwrap();
        assert_eq!(original.compilation_target(), reparsed.compilation_target());
        assert_eq!(original.commit().cmr(), reparsed.commit().cmr());
        std::fs::write(&helper, "target elements; pub fn value() -> u32 { 1 }").unwrap();
        let err =
            TemplateAst::new_with_dep(canon, &deps, &features, Box::new(SourceJetHinter::new()))
                .unwrap_err()
                .render_to_string();
        assert!(err.contains("entry source file"), "{err}");
    }
}

#[cfg(feature = "unstable-bitcoin")]
mod bitcoin {
    use super::*;
    use simplicityhl::ast::BitcoinJetHinter;
    use simplicityhl::simplicity::bitcoin::{self, secp256k1, taproot};
    use simplicityhl::simplicity::{jet::BitcoinEnv, Cmr};
    use simplicityhl::value::ValueConstructible;
    use simplicityhl::{TemplateProgramWitness, Value, WitnessNameToValueMap, WitnessValues};
    use std::collections::HashMap;

    #[test]
    fn bitcoin_compilation_uses_one_coherent_jet_set_and_requires_source() {
        let src = "target bitcoin; fn main() { let x: u64 = jet::current_value(); assert!(jet::eq_64(x, x)); }";
        let features = UnstableFeatures::new([UnstableFeature::Bitcoin]);
        let program = compile(src, &features, Box::new(SourceJetHinter::new())).unwrap();
        assert_eq!(
            program.compilation_target(),
            Some(CompilationTarget::Bitcoin)
        );
        let explicit = compile(src, &features, Box::new(BitcoinJetHinter::new())).unwrap();
        assert_eq!(program.commit().cmr(), explicit.commit().cmr());
        let err =
            compile("fn main() {}", &features, Box::new(BitcoinJetHinter::new())).unwrap_err();
        assert!(err.contains("target bitcoin;"));
        let err = compile(
            "target bitcoin; fn main() { let x: u256 = jet::current_asset(); }",
            &features,
            Box::new(SourceJetHinter::new()),
        )
        .unwrap_err();
        assert!(err.contains("current_asset"), "{err}");
    }

    fn env(tx: bitcoin::Transaction, cmr: Cmr) -> BitcoinEnv<bitcoin::Transaction> {
        let control = taproot::ControlBlock::decode(&[
            0xbe, 0x50, 0x92, 0x9b, 0x74, 0xc1, 0xa0, 0x49, 0x54, 0xb7, 0x8b, 0x4b, 0x60, 0x35,
            0xe9, 0x7a, 0x5e, 0x07, 0x8a, 0x5a, 0x0f, 0x28, 0xec, 0x96, 0xd5, 0x47, 0xbf, 0xee,
            0x9a, 0xce, 0x80, 0x3a, 0xc0,
        ])
        .unwrap();
        let prevout = bitcoin::TxOut {
            value: bitcoin::Amount::from_sat(20_000),
            script_pubkey: bitcoin::ScriptBuf::new(),
        };
        BitcoinEnv::new(tx, &[prevout], 0, cmr, control)
    }

    #[test]
    fn p2pk_satisfies_and_prunes_but_rejects_wrong_signature_transaction_or_commitment() {
        let secp = secp256k1::Secp256k1::new();
        let key = secp256k1::Keypair::from_secret_key(
            &secp,
            &secp256k1::SecretKey::from_slice(&[1; 32]).unwrap(),
        );
        let args = Arguments::from_map(HashMap::from([(
            TemplateProgramWitness::parameter_from_str("ALICE_PUBLIC_KEY"),
            Value::u256(simplicityhl::num::U256::from_byte_array(
                key.x_only_public_key().0.serialize(),
            )),
        )]));
        let program = CompiledProgram::new_with_unstable(
            include_str!("../examples/bitcoin_p2pk.simf"),
            &UnstableFeatures::new([UnstableFeature::Bitcoin]),
            args,
            false,
            Box::new(SourceJetHinter::new()),
        )
        .unwrap();
        let tx = bitcoin::Transaction {
            version: bitcoin::transaction::Version(2),
            lock_time: bitcoin::absolute::LockTime::ZERO,
            input: vec![bitcoin::TxIn {
                previous_output: bitcoin::OutPoint::null(),
                script_sig: bitcoin::ScriptBuf::new(),
                sequence: bitcoin::Sequence::MAX,
                witness: bitcoin::Witness::new(),
            }],
            output: vec![bitcoin::TxOut {
                value: bitcoin::Amount::from_sat(10_000),
                script_pubkey: bitcoin::ScriptBuf::new(),
            }],
        };
        let env_original = env(tx.clone(), program.commit().cmr());
        let message =
            secp256k1::Message::from_digest(env_original.c_tx_env().sighash_all().to_byte_array());
        let sig = secp.sign_schnorr_no_aux_rand(&message, &key).serialize();
        let witnesses = |sig| {
            WitnessValues::from_map(HashMap::from([(
                TemplateProgramWitness::witness_from_str("ALICE_SIGNATURE"),
                Value::byte_array(sig),
            )]))
        };
        let satisfied = program
            .satisfy_with_bitcoin_env(witnesses(sig), &env_original)
            .unwrap();
        let (encoded, witness) = satisfied.redeem().to_vec_with_witness();
        assert!(!encoded.is_empty() && !witness.is_empty());
        assert!(program
            .satisfy_with_bitcoin_env(witnesses([0u8; 64]), &env_original)
            .is_err());
        let mut changed = tx.clone();
        changed.output[0].value = bitcoin::Amount::from_sat(10_001);
        assert!(program
            .satisfy_with_bitcoin_env(witnesses(sig), &env(changed, program.commit().cmr()))
            .is_err());
        let err = program
            .satisfy_with_bitcoin_env(witnesses(sig), &env(tx, Cmr::from_byte_array([0; 32])))
            .unwrap_err();
        assert!(err.contains("CMR"));
        let elements = compile(
            ELEMENTS,
            &UnstableFeatures::none(),
            Box::new(SourceJetHinter::new()),
        )
        .unwrap();
        assert!(elements
            .satisfy_with_bitcoin_env(WitnessValues::default(), &env_original)
            .unwrap_err()
            .contains("Bitcoin-target"));
    }
}

#[test]
fn cli_reports_target_and_checks_both_bitcoin_gates() {
    use std::path::Path;
    use std::process::Command;
    let source = Path::new(env!("CARGO_TARGET_TMPDIR")).join("cli-source-target.simf");
    std::fs::write(&source, "target elements; fn main() {}").unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_simc"))
        .arg(&source)
        .output()
        .unwrap();
    assert!(output.status.success());
    assert!(String::from_utf8_lossy(&output.stdout).contains("Target:\nelements"));
    std::fs::write(&source, "target bitcoin; fn main() {}").unwrap();
    let disabled = Command::new(env!("CARGO_BIN_EXE_simc"))
        .arg(&source)
        .output()
        .unwrap();
    assert!(!disabled.status.success());
    assert!(String::from_utf8_lossy(&disabled.stderr).contains("-Z bitcoin"));
    let enabled = Command::new(env!("CARGO_BIN_EXE_simc"))
        .arg(&source)
        .args(["-Z", "bitcoin"])
        .output()
        .unwrap();
    if cfg!(feature = "unstable-bitcoin") {
        assert!(
            enabled.status.success(),
            "{}",
            String::from_utf8_lossy(&enabled.stderr)
        );
        assert!(String::from_utf8_lossy(&enabled.stdout).contains("Target:\nbitcoin"));
        assert!(String::from_utf8_lossy(&enabled.stderr).contains("UNSTABLE"));
    } else {
        assert!(!enabled.status.success());
        assert!(String::from_utf8_lossy(&enabled.stderr).contains("unstable-bitcoin Cargo feature"));
    }
}
