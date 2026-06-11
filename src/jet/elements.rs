use crate::types::BuiltinAlias::*;
use crate::types::UIntType::*;

use super::*;

use simplicity::jet::{Elements, Jet};

impl JetHL for Elements {
    fn source_jet_classification(&self) -> SourceJetClassification {
        source_jet_classification(*self)
    }

    fn target_jet_classification(&self) -> TargetJetClassification {
        target_jet_classification(*self)
    }

    fn is_disabled(&self) -> bool {
        matches!(self, Elements::CheckSigVerify | Elements::Verify)
    }

    fn clone_box(&self) -> Box<dyn JetHL> {
        Box::new(*self)
    }

    fn as_jet(&self) -> &dyn Jet {
        self
    }
}

fn source_jet_classification(jet: Elements) -> SourceJetClassification {
    match jet {
        /*
         * ==============================
         *          Core jets
         * ==============================
         *
         * Multi-bit logic
         */
        Elements::Low1
        | Elements::Low8
        | Elements::Low16
        | Elements::Low32
        | Elements::Low64
        | Elements::High1
        | Elements::High8
        | Elements::High16
        | Elements::High32
        | Elements::High64 => SourceJetClassification::Unary,
        Elements::Verify => SourceJetClassification::Custom(vec![bool()]),
        Elements::Complement1
        | Elements::Some1
        | Elements::LeftPadLow1_8
        | Elements::LeftPadLow1_16
        | Elements::LeftPadLow1_32
        | Elements::LeftPadLow1_64
        | Elements::LeftPadHigh1_8
        | Elements::LeftPadHigh1_16
        | Elements::LeftPadHigh1_32
        | Elements::LeftPadHigh1_64
        | Elements::LeftExtend1_8
        | Elements::LeftExtend1_16
        | Elements::LeftExtend1_32
        | Elements::LeftExtend1_64
        | Elements::RightPadLow1_8
        | Elements::RightPadLow1_16
        | Elements::RightPadLow1_32
        | Elements::RightPadLow1_64
        | Elements::RightPadHigh1_8
        | Elements::RightPadHigh1_16
        | Elements::RightPadHigh1_32
        | Elements::RightPadHigh1_64 => SourceJetClassification::Unary,
        Elements::Complement8
        | Elements::Some8
        | Elements::All8
        | Elements::Leftmost8_1
        | Elements::Leftmost8_2
        | Elements::Leftmost8_4
        | Elements::Rightmost8_1
        | Elements::Rightmost8_2
        | Elements::Rightmost8_4
        | Elements::LeftPadLow8_16
        | Elements::LeftPadLow8_32
        | Elements::LeftPadLow8_64
        | Elements::LeftPadHigh8_16
        | Elements::LeftPadHigh8_32
        | Elements::LeftPadHigh8_64
        | Elements::LeftExtend8_16
        | Elements::LeftExtend8_32
        | Elements::LeftExtend8_64
        | Elements::RightPadLow8_16
        | Elements::RightPadLow8_32
        | Elements::RightPadLow8_64
        | Elements::RightPadHigh8_16
        | Elements::RightPadHigh8_32
        | Elements::RightPadHigh8_64
        | Elements::RightExtend8_16
        | Elements::RightExtend8_32
        | Elements::RightExtend8_64 => SourceJetClassification::Unary,
        Elements::Complement16
        | Elements::Some16
        | Elements::All16
        | Elements::Leftmost16_1
        | Elements::Leftmost16_2
        | Elements::Leftmost16_4
        | Elements::Leftmost16_8
        | Elements::Rightmost16_1
        | Elements::Rightmost16_2
        | Elements::Rightmost16_4
        | Elements::Rightmost16_8
        | Elements::LeftPadLow16_32
        | Elements::LeftPadLow16_64
        | Elements::LeftPadHigh16_32
        | Elements::LeftPadHigh16_64
        | Elements::LeftExtend16_32
        | Elements::LeftExtend16_64
        | Elements::RightPadLow16_32
        | Elements::RightPadLow16_64
        | Elements::RightPadHigh16_32
        | Elements::RightPadHigh16_64
        | Elements::RightExtend16_32
        | Elements::RightExtend16_64 => SourceJetClassification::Unary,
        Elements::Complement32
        | Elements::Some32
        | Elements::All32
        | Elements::Leftmost32_1
        | Elements::Leftmost32_2
        | Elements::Leftmost32_4
        | Elements::Leftmost32_8
        | Elements::Leftmost32_16
        | Elements::Rightmost32_1
        | Elements::Rightmost32_2
        | Elements::Rightmost32_4
        | Elements::Rightmost32_8
        | Elements::Rightmost32_16
        | Elements::LeftPadLow32_64
        | Elements::LeftPadHigh32_64
        | Elements::LeftExtend32_64
        | Elements::RightPadLow32_64
        | Elements::RightPadHigh32_64
        | Elements::RightExtend32_64 => SourceJetClassification::Unary,
        Elements::Complement64
        | Elements::Some64
        | Elements::All64
        | Elements::Leftmost64_1
        | Elements::Leftmost64_2
        | Elements::Leftmost64_4
        | Elements::Leftmost64_8
        | Elements::Leftmost64_16
        | Elements::Leftmost64_32
        | Elements::Rightmost64_1
        | Elements::Rightmost64_2
        | Elements::Rightmost64_4
        | Elements::Rightmost64_8
        | Elements::Rightmost64_16
        | Elements::Rightmost64_32 => SourceJetClassification::Unary,
        Elements::And1 | Elements::Or1 | Elements::Xor1 | Elements::Eq1 => {
            SourceJetClassification::Binary
        }
        Elements::And8 | Elements::Or8 | Elements::Xor8 | Elements::Eq8 => {
            SourceJetClassification::Binary
        }
        Elements::And16 | Elements::Or16 | Elements::Xor16 | Elements::Eq16 => {
            SourceJetClassification::Binary
        }
        Elements::And32 | Elements::Or32 | Elements::Xor32 | Elements::Eq32 => {
            SourceJetClassification::Binary
        }
        Elements::And64 | Elements::Or64 | Elements::Xor64 | Elements::Eq64 => {
            SourceJetClassification::Binary
        }
        Elements::Eq256 => SourceJetClassification::Binary,
        Elements::Maj1 | Elements::XorXor1 | Elements::Ch1 => SourceJetClassification::Ternary,
        Elements::Maj8 | Elements::XorXor8 | Elements::Ch8 => SourceJetClassification::Ternary,
        Elements::Maj16 | Elements::XorXor16 | Elements::Ch16 => {
            SourceJetClassification::Custom(vec![U16.into(), tuple([U16, U16])])
        }
        Elements::Maj32 | Elements::XorXor32 | Elements::Ch32 => {
            SourceJetClassification::Custom(vec![U32.into(), tuple([U32, U32])])
        }
        Elements::Maj64 | Elements::XorXor64 | Elements::Ch64 => {
            SourceJetClassification::Custom(vec![U64.into(), tuple([U64, U64])])
        }
        Elements::FullLeftShift8_1 => SourceJetClassification::Custom(vec![U8.into(), U1.into()]),
        Elements::FullLeftShift8_2 => SourceJetClassification::Custom(vec![U8.into(), U2.into()]),
        Elements::FullLeftShift8_4 => SourceJetClassification::Custom(vec![U8.into(), U4.into()]),
        Elements::FullLeftShift16_1 => SourceJetClassification::Custom(vec![U16.into(), U1.into()]),
        Elements::FullLeftShift16_2 => SourceJetClassification::Custom(vec![U16.into(), U2.into()]),
        Elements::FullLeftShift16_4 => SourceJetClassification::Custom(vec![U16.into(), U4.into()]),
        Elements::FullLeftShift16_8 => SourceJetClassification::Custom(vec![U16.into(), U8.into()]),
        Elements::FullLeftShift32_1 => SourceJetClassification::Custom(vec![U32.into(), U1.into()]),
        Elements::FullLeftShift32_2 => SourceJetClassification::Custom(vec![U32.into(), U2.into()]),
        Elements::FullLeftShift32_4 => SourceJetClassification::Custom(vec![U32.into(), U4.into()]),
        Elements::FullLeftShift32_8 => SourceJetClassification::Custom(vec![U32.into(), U8.into()]),
        Elements::FullLeftShift32_16 => {
            SourceJetClassification::Custom(vec![U32.into(), U16.into()])
        }
        Elements::FullLeftShift64_1 => SourceJetClassification::Custom(vec![U64.into(), U1.into()]),
        Elements::FullLeftShift64_2 => SourceJetClassification::Custom(vec![U64.into(), U2.into()]),
        Elements::FullLeftShift64_4 => SourceJetClassification::Custom(vec![U64.into(), U4.into()]),
        Elements::FullLeftShift64_8 => SourceJetClassification::Custom(vec![U64.into(), U8.into()]),
        Elements::FullLeftShift64_16 => {
            SourceJetClassification::Custom(vec![U64.into(), U16.into()])
        }
        Elements::FullLeftShift64_32 => {
            SourceJetClassification::Custom(vec![U64.into(), U32.into()])
        }
        Elements::FullRightShift8_1 => SourceJetClassification::Custom(vec![U1.into(), U8.into()]),
        Elements::FullRightShift8_2 => SourceJetClassification::Custom(vec![U2.into(), U8.into()]),
        Elements::FullRightShift8_4 => SourceJetClassification::Custom(vec![U4.into(), U8.into()]),
        Elements::FullRightShift16_1 => {
            SourceJetClassification::Custom(vec![U1.into(), U16.into()])
        }
        Elements::FullRightShift16_2 => {
            SourceJetClassification::Custom(vec![U2.into(), U16.into()])
        }
        Elements::FullRightShift16_4 => {
            SourceJetClassification::Custom(vec![U4.into(), U16.into()])
        }
        Elements::FullRightShift16_8 => {
            SourceJetClassification::Custom(vec![U8.into(), U16.into()])
        }
        Elements::FullRightShift32_1 => {
            SourceJetClassification::Custom(vec![U1.into(), U32.into()])
        }
        Elements::FullRightShift32_2 => {
            SourceJetClassification::Custom(vec![U2.into(), U32.into()])
        }
        Elements::FullRightShift32_4 => {
            SourceJetClassification::Custom(vec![U4.into(), U32.into()])
        }
        Elements::FullRightShift32_8 => {
            SourceJetClassification::Custom(vec![U8.into(), U32.into()])
        }
        Elements::FullRightShift32_16 => {
            SourceJetClassification::Custom(vec![U16.into(), U32.into()])
        }
        Elements::FullRightShift64_1 => {
            SourceJetClassification::Custom(vec![U1.into(), U64.into()])
        }
        Elements::FullRightShift64_2 => {
            SourceJetClassification::Custom(vec![U2.into(), U64.into()])
        }
        Elements::FullRightShift64_4 => {
            SourceJetClassification::Custom(vec![U4.into(), U64.into()])
        }
        Elements::FullRightShift64_8 => {
            SourceJetClassification::Custom(vec![U8.into(), U64.into()])
        }
        Elements::FullRightShift64_16 => {
            SourceJetClassification::Custom(vec![U16.into(), U64.into()])
        }
        Elements::FullRightShift64_32 => {
            SourceJetClassification::Custom(vec![U32.into(), U64.into()])
        }
        Elements::LeftShiftWith8 | Elements::RightShiftWith8 => {
            SourceJetClassification::Custom(vec![U1.into(), U4.into(), U8.into()])
        }
        Elements::LeftShiftWith16 | Elements::RightShiftWith16 => {
            SourceJetClassification::Custom(vec![U1.into(), U4.into(), U16.into()])
        }
        Elements::LeftShiftWith32 | Elements::RightShiftWith32 => {
            SourceJetClassification::Custom(vec![U1.into(), U8.into(), U32.into()])
        }
        Elements::LeftShiftWith64 | Elements::RightShiftWith64 => {
            SourceJetClassification::Custom(vec![U1.into(), U8.into(), U64.into()])
        }
        Elements::LeftShift8
        | Elements::RightShift8
        | Elements::LeftRotate8
        | Elements::RightRotate8 => SourceJetClassification::Custom(vec![U4.into(), U8.into()]),
        Elements::LeftShift16
        | Elements::RightShift16
        | Elements::LeftRotate16
        | Elements::RightRotate16 => SourceJetClassification::Custom(vec![U4.into(), U16.into()]),
        Elements::LeftShift32
        | Elements::RightShift32
        | Elements::LeftRotate32
        | Elements::RightRotate32 => SourceJetClassification::Custom(vec![U8.into(), U32.into()]),
        Elements::LeftShift64
        | Elements::RightShift64
        | Elements::LeftRotate64
        | Elements::RightRotate64 => SourceJetClassification::Custom(vec![U8.into(), U64.into()]),
        /*
         * Arithmetic
         */
        Elements::One8 | Elements::One16 | Elements::One32 | Elements::One64 => {
            SourceJetClassification::Unary
        }
        Elements::Increment8
        | Elements::Negate8
        | Elements::Decrement8
        | Elements::IsZero8
        | Elements::IsOne8 => SourceJetClassification::Unary,
        Elements::Increment16
        | Elements::Negate16
        | Elements::Decrement16
        | Elements::IsZero16
        | Elements::IsOne16 => SourceJetClassification::Unary,
        Elements::Increment32
        | Elements::Negate32
        | Elements::Decrement32
        | Elements::IsZero32
        | Elements::IsOne32 => SourceJetClassification::Unary,
        Elements::Increment64
        | Elements::Negate64
        | Elements::Decrement64
        | Elements::IsZero64
        | Elements::IsOne64 => SourceJetClassification::Unary,
        Elements::Add8
        | Elements::Subtract8
        | Elements::Multiply8
        | Elements::Le8
        | Elements::Lt8
        | Elements::Min8
        | Elements::Max8
        | Elements::DivMod8
        | Elements::Divide8
        | Elements::Modulo8
        | Elements::Divides8 => SourceJetClassification::Binary,
        Elements::Add16
        | Elements::Subtract16
        | Elements::Multiply16
        | Elements::Le16
        | Elements::Lt16
        | Elements::Min16
        | Elements::Max16
        | Elements::DivMod16
        | Elements::Divide16
        | Elements::Modulo16
        | Elements::Divides16 => SourceJetClassification::Binary,
        Elements::Add32
        | Elements::Subtract32
        | Elements::Multiply32
        | Elements::Le32
        | Elements::Lt32
        | Elements::Min32
        | Elements::Max32
        | Elements::DivMod32
        | Elements::Divide32
        | Elements::Modulo32
        | Elements::Divides32 => SourceJetClassification::Binary,
        Elements::Add64
        | Elements::Subtract64
        | Elements::Multiply64
        | Elements::Le64
        | Elements::Lt64
        | Elements::Min64
        | Elements::Max64
        | Elements::DivMod64
        | Elements::Divide64
        | Elements::Modulo64
        | Elements::Divides64 => SourceJetClassification::Binary,
        Elements::DivMod128_64 => SourceJetClassification::Custom(vec![U128.into(), U64.into()]),
        Elements::FullAdd8 | Elements::FullSubtract8 => {
            SourceJetClassification::Custom(vec![bool(), U8.into(), U8.into()])
        }
        Elements::FullAdd16 | Elements::FullSubtract16 => {
            SourceJetClassification::Custom(vec![bool(), U16.into(), U16.into()])
        }
        Elements::FullAdd32 | Elements::FullSubtract32 => {
            SourceJetClassification::Custom(vec![bool(), U32.into(), U32.into()])
        }
        Elements::FullAdd64 | Elements::FullSubtract64 => {
            SourceJetClassification::Custom(vec![bool(), U64.into(), U64.into()])
        }
        Elements::FullIncrement8 | Elements::FullDecrement8 => {
            SourceJetClassification::Custom(vec![bool(), U8.into()])
        }
        Elements::FullIncrement16 | Elements::FullDecrement16 => {
            SourceJetClassification::Custom(vec![bool(), U16.into()])
        }
        Elements::FullIncrement32 | Elements::FullDecrement32 => {
            SourceJetClassification::Custom(vec![bool(), U32.into()])
        }
        Elements::FullIncrement64 | Elements::FullDecrement64 => {
            SourceJetClassification::Custom(vec![bool(), U64.into()])
        }
        Elements::FullMultiply8 => SourceJetClassification::Quaternary,
        Elements::FullMultiply16 => SourceJetClassification::Quaternary,
        Elements::FullMultiply32 => SourceJetClassification::Quaternary,
        Elements::FullMultiply64 => SourceJetClassification::Quaternary,
        Elements::Median8 => SourceJetClassification::Ternary,
        Elements::Median16 => SourceJetClassification::Ternary,
        Elements::Median32 => SourceJetClassification::Ternary,
        Elements::Median64 => SourceJetClassification::Ternary,
        /*
         * Hash functions
         */
        Elements::Sha256Iv | Elements::Sha256Ctx8Init => SourceJetClassification::Unary,
        Elements::Sha256Block => SourceJetClassification::Ternary,
        Elements::Sha256Ctx8Add1 => SourceJetClassification::Custom(vec![Ctx8.into(), U8.into()]),
        Elements::Sha256Ctx8Add2 => SourceJetClassification::Custom(vec![Ctx8.into(), U16.into()]),
        Elements::Sha256Ctx8Add4 => SourceJetClassification::Custom(vec![Ctx8.into(), U32.into()]),
        Elements::Sha256Ctx8Add8 => SourceJetClassification::Custom(vec![Ctx8.into(), U64.into()]),
        Elements::Sha256Ctx8Add16 => {
            SourceJetClassification::Custom(vec![Ctx8.into(), U128.into()])
        }
        Elements::Sha256Ctx8Add32 => {
            SourceJetClassification::Custom(vec![Ctx8.into(), U256.into()])
        }
        Elements::Sha256Ctx8Add64 => {
            SourceJetClassification::Custom(vec![Ctx8.into(), array(U8, 64)])
        }
        Elements::Sha256Ctx8Add128 => {
            SourceJetClassification::Custom(vec![Ctx8.into(), array(U8, 128)])
        }
        Elements::Sha256Ctx8Add256 => {
            SourceJetClassification::Custom(vec![Ctx8.into(), array(U8, 256)])
        }
        Elements::Sha256Ctx8Add512 => {
            SourceJetClassification::Custom(vec![Ctx8.into(), array(U8, 512)])
        }
        Elements::Sha256Ctx8AddBuffer511 => {
            SourceJetClassification::Custom(vec![Ctx8.into(), list(U8, 512)])
        }
        Elements::Sha256Ctx8Finalize => SourceJetClassification::Custom(vec![Ctx8.into()]),
        /*
         * Elliptic curve functions
         */
        // XXX: Nonstandard tuple
        Elements::PointVerify1 => SourceJetClassification::Custom(vec![
            tuple([tuple([Scalar, Point]), Scalar.into()]),
            Point.into(),
        ]),
        Elements::Decompress => SourceJetClassification::Custom(vec![Point.into()]),
        // XXX: Nonstandard tuple
        Elements::LinearVerify1 => SourceJetClassification::Custom(vec![
            tuple([tuple([Scalar, Ge]), Scalar.into()]),
            Ge.into(),
        ]),
        // XXX: Nonstandard tuple
        Elements::LinearCombination1 => {
            SourceJetClassification::Custom(vec![tuple([Scalar, Gej]), Scalar.into()])
        }
        Elements::Scale => SourceJetClassification::Custom(vec![Scalar.into(), Gej.into()]),
        Elements::Generate => SourceJetClassification::Custom(vec![Scalar.into()]),
        Elements::GejInfinity => SourceJetClassification::Unary,
        Elements::GejNormalize
        | Elements::GejNegate
        | Elements::GejDouble
        | Elements::GejIsInfinity
        | Elements::GejYIsOdd
        | Elements::GejIsOnCurve => SourceJetClassification::Custom(vec![Gej.into()]),
        Elements::GeNegate | Elements::GeIsOnCurve => {
            SourceJetClassification::Custom(vec![Ge.into()])
        }
        Elements::GejAdd | Elements::GejEquiv => {
            SourceJetClassification::Custom(vec![Gej.into(), Gej.into()])
        }
        Elements::GejGeAddEx | Elements::GejGeAdd | Elements::GejGeEquiv => {
            SourceJetClassification::Custom(vec![Gej.into(), Ge.into()])
        }
        Elements::GejRescale => SourceJetClassification::Custom(vec![Gej.into(), Fe.into()]),
        Elements::GejXEquiv => SourceJetClassification::Custom(vec![Fe.into(), Gej.into()]),
        Elements::ScalarAdd | Elements::ScalarMultiply => {
            SourceJetClassification::Custom(vec![Scalar.into(), Scalar.into()])
        }
        Elements::ScalarNormalize
        | Elements::ScalarNegate
        | Elements::ScalarSquare
        | Elements::ScalarInvert
        | Elements::ScalarMultiplyLambda
        | Elements::ScalarIsZero => SourceJetClassification::Custom(vec![Scalar.into()]),
        Elements::FeNormalize
        | Elements::FeNegate
        | Elements::FeSquare
        | Elements::FeMultiplyBeta
        | Elements::FeInvert
        | Elements::FeSquareRoot
        | Elements::FeIsZero
        | Elements::FeIsOdd
        | Elements::Swu => SourceJetClassification::Custom(vec![Fe.into()]),
        Elements::FeAdd | Elements::FeMultiply => {
            SourceJetClassification::Custom(vec![Fe.into(), Fe.into()])
        }
        Elements::HashToCurve => SourceJetClassification::Unary,
        /*
         * Digital signatures
         */
        // XXX: Nonstandard tuple
        Elements::CheckSigVerify => {
            SourceJetClassification::Custom(vec![tuple([Pubkey, Message64]), Signature.into()])
        }
        // XXX: Nonstandard tuple
        Elements::Bip0340Verify => {
            SourceJetClassification::Custom(vec![tuple([Pubkey, Message]), Signature.into()])
        }
        /*
         * Bitcoin (without primitives)
         */
        Elements::TapdataInit => SourceJetClassification::Unary,
        Elements::ParseLock | Elements::ParseSequence => SourceJetClassification::Unary,
        /*
         * ==============================
         *         Elements jets
         * ==============================
         *
         * Signature hash modes
         */
        Elements::SigAllHash
        | Elements::TxHash
        | Elements::TapEnvHash
        | Elements::InputsHash
        | Elements::OutputsHash
        | Elements::IssuancesHash
        | Elements::InputUtxosHash
        | Elements::OutputAmountsHash
        | Elements::OutputScriptsHash
        | Elements::OutputNoncesHash
        | Elements::OutputRangeProofsHash
        | Elements::OutputSurjectionProofsHash
        | Elements::InputOutpointsHash
        | Elements::InputAnnexesHash
        | Elements::InputSequencesHash
        | Elements::InputScriptSigsHash
        | Elements::IssuanceAssetAmountsHash
        | Elements::IssuanceTokenAmountsHash
        | Elements::IssuanceRangeProofsHash
        | Elements::IssuanceBlindingEntropyHash
        | Elements::InputAmountsHash
        | Elements::InputScriptsHash
        | Elements::TapleafHash
        | Elements::TappathHash => SourceJetClassification::Unary,
        Elements::OutpointHash => {
            SourceJetClassification::Custom(vec![Ctx8.into(), option(U256), Outpoint.into()])
        }
        Elements::AssetAmountHash => {
            SourceJetClassification::Custom(vec![Ctx8.into(), Asset1.into(), Amount1.into()])
        }
        Elements::NonceHash => SourceJetClassification::Custom(vec![Ctx8.into(), option(Nonce)]),
        Elements::AnnexHash => SourceJetClassification::Custom(vec![Ctx8.into(), option(U256)]),
        Elements::BuildTapleafSimplicity => SourceJetClassification::Unary,
        Elements::BuildTapbranch => SourceJetClassification::Binary,
        Elements::BuildTaptweak => {
            SourceJetClassification::Custom(vec![Pubkey.into(), U256.into()])
        }
        /*
         * Time locks
         */
        Elements::CheckLockTime => SourceJetClassification::Custom(vec![Time.into()]),
        Elements::BrokenDoNotUseCheckLockDistance => {
            SourceJetClassification::Custom(vec![Distance.into()])
        }
        Elements::BrokenDoNotUseCheckLockDuration => {
            SourceJetClassification::Custom(vec![Duration.into()])
        }
        Elements::CheckLockHeight => SourceJetClassification::Custom(vec![Height.into()]),
        Elements::TxLockTime
        | Elements::BrokenDoNotUseTxLockDistance
        | Elements::BrokenDoNotUseTxLockDuration
        | Elements::TxLockHeight
        | Elements::TxIsFinal => SourceJetClassification::Unary,
        /*
         * Issuance
         */
        Elements::Issuance
        | Elements::IssuanceAsset
        | Elements::IssuanceToken
        | Elements::IssuanceEntropy => SourceJetClassification::Unary,
        Elements::CalculateIssuanceEntropy => {
            SourceJetClassification::Custom(vec![Outpoint.into(), U256.into()])
        }
        Elements::CalculateAsset
        | Elements::CalculateExplicitToken
        | Elements::CalculateConfidentialToken => SourceJetClassification::Unary,
        /*
         * Transaction
         */
        Elements::ScriptCMR
        | Elements::InternalKey
        | Elements::CurrentIndex
        | Elements::NumInputs
        | Elements::NumOutputs
        | Elements::LockTime
        | Elements::CurrentPegin
        | Elements::CurrentPrevOutpoint
        | Elements::CurrentAsset
        | Elements::CurrentAmount
        | Elements::CurrentScriptHash
        | Elements::CurrentSequence
        | Elements::CurrentAnnexHash
        | Elements::CurrentScriptSigHash
        | Elements::CurrentReissuanceBlinding
        | Elements::CurrentNewIssuanceContract
        | Elements::CurrentReissuanceEntropy
        | Elements::CurrentIssuanceTokenAmount
        | Elements::CurrentIssuanceAssetAmount
        | Elements::CurrentIssuanceAssetProof
        | Elements::CurrentIssuanceTokenProof
        | Elements::TapleafVersion
        | Elements::Version
        | Elements::GenesisBlockHash
        | Elements::LbtcAsset
        | Elements::TransactionId => SourceJetClassification::Unary,
        Elements::OutputAsset
        | Elements::OutputAmount
        | Elements::OutputNonce
        | Elements::OutputScriptHash
        | Elements::OutputIsFee
        | Elements::OutputSurjectionProof
        | Elements::OutputRangeProof
        | Elements::OutputHash
        | Elements::InputPegin
        | Elements::InputPrevOutpoint
        | Elements::InputAsset
        | Elements::InputAmount
        | Elements::InputScriptHash
        | Elements::InputSequence
        | Elements::InputAnnexHash
        | Elements::InputScriptSigHash
        | Elements::InputHash
        | Elements::InputUtxoHash
        | Elements::ReissuanceBlinding
        | Elements::NewIssuanceContract
        | Elements::ReissuanceEntropy
        | Elements::IssuanceAssetAmount
        | Elements::IssuanceTokenAmount
        | Elements::IssuanceAssetProof
        | Elements::IssuanceTokenProof
        | Elements::IssuanceHash => SourceJetClassification::Unary,
        Elements::OutputNullDatum => SourceJetClassification::Binary,
        Elements::TotalFee => SourceJetClassification::Custom(vec![ExplicitAsset.into()]),
        Elements::Tappath => SourceJetClassification::Unary,
    }
}

fn target_jet_classification(jet: Elements) -> TargetJetClassification {
    match jet {
        /*
         * ==============================
         *          Core jets
         * ==============================
         *
         * Multi-bit logic
         */
        Elements::Verify => TargetJetClassification::Unary,
        Elements::Some1
        | Elements::Some8
        | Elements::Some16
        | Elements::Some32
        | Elements::Some64
        | Elements::All8
        | Elements::All16
        | Elements::All32
        | Elements::All64
        | Elements::Eq1
        | Elements::Eq8
        | Elements::Eq16
        | Elements::Eq32
        | Elements::Eq64
        | Elements::Eq256 => TargetJetClassification::Custom(bool()),
        Elements::Low1
        | Elements::High1
        | Elements::Complement1
        | Elements::And1
        | Elements::Or1
        | Elements::Xor1
        | Elements::Maj1
        | Elements::XorXor1
        | Elements::Ch1
        | Elements::Leftmost8_1
        | Elements::Rightmost8_1
        | Elements::Leftmost16_1
        | Elements::Rightmost16_1
        | Elements::Leftmost32_1
        | Elements::Rightmost32_1
        | Elements::Leftmost64_1
        | Elements::Rightmost64_1 => TargetJetClassification::Unary,
        Elements::Leftmost8_2
        | Elements::Rightmost8_2
        | Elements::Leftmost16_2
        | Elements::Rightmost16_2
        | Elements::Leftmost32_2
        | Elements::Rightmost32_2
        | Elements::Leftmost64_2
        | Elements::Rightmost64_2 => TargetJetClassification::Unary,
        Elements::Leftmost8_4
        | Elements::Rightmost8_4
        | Elements::Leftmost16_4
        | Elements::Rightmost16_4
        | Elements::Leftmost32_4
        | Elements::Rightmost32_4
        | Elements::Leftmost64_4
        | Elements::Rightmost64_4 => TargetJetClassification::Unary,
        Elements::Low8
        | Elements::High8
        | Elements::Complement8
        | Elements::And8
        | Elements::Or8
        | Elements::Xor8
        | Elements::Maj8
        | Elements::XorXor8
        | Elements::Ch8
        | Elements::Leftmost16_8
        | Elements::Rightmost16_8
        | Elements::Leftmost32_8
        | Elements::Rightmost32_8
        | Elements::Leftmost64_8
        | Elements::Rightmost64_8
        | Elements::LeftPadLow1_8
        | Elements::LeftPadHigh1_8
        | Elements::LeftExtend1_8
        | Elements::RightPadLow1_8
        | Elements::RightPadHigh1_8
        | Elements::LeftShiftWith8
        | Elements::RightShiftWith8
        | Elements::LeftShift8
        | Elements::RightShift8
        | Elements::LeftRotate8
        | Elements::RightRotate8 => TargetJetClassification::Unary,
        Elements::Low16
        | Elements::High16
        | Elements::Complement16
        | Elements::And16
        | Elements::Or16
        | Elements::Xor16
        | Elements::Maj16
        | Elements::XorXor16
        | Elements::Ch16
        | Elements::Leftmost32_16
        | Elements::Rightmost32_16
        | Elements::Leftmost64_16
        | Elements::Rightmost64_16
        | Elements::LeftPadLow1_16
        | Elements::LeftPadHigh1_16
        | Elements::LeftExtend1_16
        | Elements::RightPadLow1_16
        | Elements::RightPadHigh1_16
        | Elements::LeftPadLow8_16
        | Elements::LeftPadHigh8_16
        | Elements::LeftExtend8_16
        | Elements::RightPadLow8_16
        | Elements::RightPadHigh8_16
        | Elements::RightExtend8_16
        | Elements::LeftShiftWith16
        | Elements::RightShiftWith16
        | Elements::LeftShift16
        | Elements::RightShift16
        | Elements::LeftRotate16
        | Elements::RightRotate16 => TargetJetClassification::Unary,
        Elements::Low32
        | Elements::High32
        | Elements::Complement32
        | Elements::And32
        | Elements::Or32
        | Elements::Xor32
        | Elements::Maj32
        | Elements::XorXor32
        | Elements::Ch32
        | Elements::Leftmost64_32
        | Elements::Rightmost64_32
        | Elements::LeftPadLow1_32
        | Elements::LeftPadHigh1_32
        | Elements::LeftExtend1_32
        | Elements::RightPadLow1_32
        | Elements::RightPadHigh1_32
        | Elements::LeftPadLow8_32
        | Elements::LeftPadHigh8_32
        | Elements::LeftExtend8_32
        | Elements::RightPadLow8_32
        | Elements::RightPadHigh8_32
        | Elements::RightExtend8_32
        | Elements::LeftPadLow16_32
        | Elements::LeftPadHigh16_32
        | Elements::LeftExtend16_32
        | Elements::RightPadLow16_32
        | Elements::RightPadHigh16_32
        | Elements::RightExtend16_32
        | Elements::LeftShiftWith32
        | Elements::RightShiftWith32
        | Elements::LeftShift32
        | Elements::RightShift32
        | Elements::LeftRotate32
        | Elements::RightRotate32 => TargetJetClassification::Unary,
        Elements::Low64
        | Elements::High64
        | Elements::Complement64
        | Elements::And64
        | Elements::Or64
        | Elements::Xor64
        | Elements::Maj64
        | Elements::XorXor64
        | Elements::Ch64
        | Elements::LeftPadLow1_64
        | Elements::LeftPadHigh1_64
        | Elements::LeftExtend1_64
        | Elements::RightPadLow1_64
        | Elements::RightPadHigh1_64
        | Elements::LeftPadLow8_64
        | Elements::LeftPadHigh8_64
        | Elements::LeftExtend8_64
        | Elements::RightPadLow8_64
        | Elements::RightPadHigh8_64
        | Elements::RightExtend8_64
        | Elements::LeftPadLow16_64
        | Elements::LeftPadHigh16_64
        | Elements::LeftExtend16_64
        | Elements::RightPadLow16_64
        | Elements::RightPadHigh16_64
        | Elements::RightExtend16_64
        | Elements::LeftPadLow32_64
        | Elements::LeftPadHigh32_64
        | Elements::LeftExtend32_64
        | Elements::RightPadLow32_64
        | Elements::RightPadHigh32_64
        | Elements::RightExtend32_64
        | Elements::LeftShiftWith64
        | Elements::RightShiftWith64
        | Elements::LeftShift64
        | Elements::RightShift64
        | Elements::LeftRotate64
        | Elements::RightRotate64 => TargetJetClassification::Unary,
        Elements::FullLeftShift8_1 => TargetJetClassification::Custom(tuple([U1, U8])),
        Elements::FullLeftShift8_2 => TargetJetClassification::Custom(tuple([U2, U8])),
        Elements::FullLeftShift8_4 => TargetJetClassification::Custom(tuple([U4, U8])),
        Elements::FullLeftShift16_1 => TargetJetClassification::Custom(tuple([U1, U16])),
        Elements::FullLeftShift16_2 => TargetJetClassification::Custom(tuple([U2, U16])),
        Elements::FullLeftShift16_4 => TargetJetClassification::Custom(tuple([U4, U16])),
        Elements::FullLeftShift16_8 => TargetJetClassification::Custom(tuple([U8, U16])),
        Elements::FullLeftShift32_1 => TargetJetClassification::Custom(tuple([U1, U32])),
        Elements::FullLeftShift32_2 => TargetJetClassification::Custom(tuple([U2, U32])),
        Elements::FullLeftShift32_4 => TargetJetClassification::Custom(tuple([U4, U32])),
        Elements::FullLeftShift32_8 => TargetJetClassification::Custom(tuple([U8, U32])),
        Elements::FullLeftShift32_16 => TargetJetClassification::Custom(tuple([U16, U32])),
        Elements::FullLeftShift64_1 => TargetJetClassification::Custom(tuple([U1, U64])),
        Elements::FullLeftShift64_2 => TargetJetClassification::Custom(tuple([U2, U64])),
        Elements::FullLeftShift64_4 => TargetJetClassification::Custom(tuple([U4, U64])),
        Elements::FullLeftShift64_8 => TargetJetClassification::Custom(tuple([U8, U64])),
        Elements::FullLeftShift64_16 => TargetJetClassification::Custom(tuple([U16, U64])),
        Elements::FullLeftShift64_32 => TargetJetClassification::Custom(tuple([U32, U64])),
        Elements::FullRightShift8_1 => TargetJetClassification::Custom(tuple([U8, U1])),
        Elements::FullRightShift8_2 => TargetJetClassification::Custom(tuple([U8, U2])),
        Elements::FullRightShift8_4 => TargetJetClassification::Custom(tuple([U8, U4])),
        Elements::FullRightShift16_1 => TargetJetClassification::Custom(tuple([U16, U1])),
        Elements::FullRightShift16_2 => TargetJetClassification::Custom(tuple([U16, U2])),
        Elements::FullRightShift16_4 => TargetJetClassification::Custom(tuple([U16, U4])),
        Elements::FullRightShift16_8 => TargetJetClassification::Custom(tuple([U16, U8])),
        Elements::FullRightShift32_1 => TargetJetClassification::Custom(tuple([U32, U1])),
        Elements::FullRightShift32_2 => TargetJetClassification::Custom(tuple([U32, U2])),
        Elements::FullRightShift32_4 => TargetJetClassification::Custom(tuple([U32, U4])),
        Elements::FullRightShift32_8 => TargetJetClassification::Custom(tuple([U32, U8])),
        Elements::FullRightShift32_16 => TargetJetClassification::Custom(tuple([U32, U16])),
        Elements::FullRightShift64_1 => TargetJetClassification::Custom(tuple([U64, U1])),
        Elements::FullRightShift64_2 => TargetJetClassification::Custom(tuple([U64, U2])),
        Elements::FullRightShift64_4 => TargetJetClassification::Custom(tuple([U64, U4])),
        Elements::FullRightShift64_8 => TargetJetClassification::Custom(tuple([U64, U8])),
        Elements::FullRightShift64_16 => TargetJetClassification::Custom(tuple([U64, U16])),
        Elements::FullRightShift64_32 => TargetJetClassification::Custom(tuple([U64, U32])),
        /*
         * Arithmetic
         */
        Elements::Le8
        | Elements::Lt8
        | Elements::Le16
        | Elements::Lt16
        | Elements::Le32
        | Elements::Lt32
        | Elements::Le64
        | Elements::Lt64
        | Elements::IsZero8
        | Elements::IsOne8
        | Elements::IsZero16
        | Elements::IsOne16
        | Elements::IsZero32
        | Elements::IsOne32
        | Elements::IsZero64
        | Elements::IsOne64
        | Elements::Divides8
        | Elements::Divides16
        | Elements::Divides32
        | Elements::Divides64 => TargetJetClassification::Custom(bool()),
        Elements::One8
        | Elements::Min8
        | Elements::Max8
        | Elements::Divide8
        | Elements::Modulo8
        | Elements::Median8 => TargetJetClassification::Unary,
        Elements::One16
        | Elements::Min16
        | Elements::Max16
        | Elements::Divide16
        | Elements::Modulo16
        | Elements::Multiply8
        | Elements::FullMultiply8
        | Elements::Median16 => TargetJetClassification::Unary,
        Elements::One32
        | Elements::Min32
        | Elements::Max32
        | Elements::Divide32
        | Elements::Modulo32
        | Elements::Multiply16
        | Elements::FullMultiply16
        | Elements::Median32 => TargetJetClassification::Unary,
        Elements::One64
        | Elements::Min64
        | Elements::Max64
        | Elements::Divide64
        | Elements::Modulo64
        | Elements::Multiply32
        | Elements::FullMultiply32
        | Elements::Median64 => TargetJetClassification::Unary,
        Elements::Multiply64 | Elements::FullMultiply64 => TargetJetClassification::Unary,
        Elements::Increment8
        | Elements::Negate8
        | Elements::Decrement8
        | Elements::Add8
        | Elements::Subtract8
        | Elements::FullAdd8
        | Elements::FullSubtract8
        | Elements::FullIncrement8
        | Elements::FullDecrement8 => TargetJetClassification::Custom(tuple([bool(), U8.into()])),
        Elements::Increment16
        | Elements::Negate16
        | Elements::Decrement16
        | Elements::Add16
        | Elements::Subtract16
        | Elements::FullAdd16
        | Elements::FullSubtract16
        | Elements::FullIncrement16
        | Elements::FullDecrement16 => TargetJetClassification::Custom(tuple([bool(), U16.into()])),
        Elements::Increment32
        | Elements::Negate32
        | Elements::Decrement32
        | Elements::Add32
        | Elements::Subtract32
        | Elements::FullAdd32
        | Elements::FullSubtract32
        | Elements::FullIncrement32
        | Elements::FullDecrement32 => TargetJetClassification::Custom(tuple([bool(), U32.into()])),
        Elements::Increment64
        | Elements::Negate64
        | Elements::Decrement64
        | Elements::Add64
        | Elements::Subtract64
        | Elements::FullAdd64
        | Elements::FullSubtract64
        | Elements::FullIncrement64
        | Elements::FullDecrement64 => TargetJetClassification::Custom(tuple([bool(), U64.into()])),
        Elements::DivMod8 => TargetJetClassification::Custom(tuple([U8, U8])),
        Elements::DivMod16 => TargetJetClassification::Custom(tuple([U16, U16])),
        Elements::DivMod32 => TargetJetClassification::Custom(tuple([U32, U32])),
        Elements::DivMod64 => TargetJetClassification::Custom(tuple([U64, U64])),
        Elements::DivMod128_64 => TargetJetClassification::Custom(tuple([U64, U64])),
        /*
         * Hash functions
         */
        Elements::Sha256Iv | Elements::Sha256Block | Elements::Sha256Ctx8Finalize => {
            TargetJetClassification::Unary
        }
        Elements::Sha256Ctx8Init
        | Elements::Sha256Ctx8Add1
        | Elements::Sha256Ctx8Add2
        | Elements::Sha256Ctx8Add4
        | Elements::Sha256Ctx8Add8
        | Elements::Sha256Ctx8Add16
        | Elements::Sha256Ctx8Add32
        | Elements::Sha256Ctx8Add64
        | Elements::Sha256Ctx8Add128
        | Elements::Sha256Ctx8Add256
        | Elements::Sha256Ctx8Add512
        | Elements::Sha256Ctx8AddBuffer511 => TargetJetClassification::Custom(Ctx8.into()),
        /*
         * Elliptic curve functions
         */
        Elements::PointVerify1 | Elements::LinearVerify1 => TargetJetClassification::Unary,
        Elements::GejIsInfinity
        | Elements::GejEquiv
        | Elements::GejGeEquiv
        | Elements::GejXEquiv
        | Elements::GejYIsOdd
        | Elements::GejIsOnCurve
        | Elements::GeIsOnCurve
        | Elements::ScalarIsZero
        | Elements::FeIsZero
        | Elements::FeIsOdd => TargetJetClassification::Custom(bool()),
        Elements::GeNegate | Elements::HashToCurve | Elements::Swu => {
            TargetJetClassification::Custom(Ge.into())
        }
        Elements::Decompress | Elements::GejNormalize => {
            TargetJetClassification::Custom(option(Ge))
        }
        Elements::LinearCombination1
        | Elements::Scale
        | Elements::Generate
        | Elements::GejInfinity
        | Elements::GejNegate
        | Elements::GejDouble
        | Elements::GejAdd
        | Elements::GejGeAdd
        | Elements::GejRescale => TargetJetClassification::Custom(Gej.into()),
        Elements::GejGeAddEx => TargetJetClassification::Custom(tuple([Fe, Gej])),
        Elements::ScalarNormalize
        | Elements::ScalarNegate
        | Elements::ScalarAdd
        | Elements::ScalarSquare
        | Elements::ScalarMultiply
        | Elements::ScalarMultiplyLambda
        | Elements::ScalarInvert => TargetJetClassification::Custom(Scalar.into()),
        Elements::FeNormalize
        | Elements::FeNegate
        | Elements::FeAdd
        | Elements::FeSquare
        | Elements::FeMultiply
        | Elements::FeMultiplyBeta
        | Elements::FeInvert => TargetJetClassification::Custom(Fe.into()),
        Elements::FeSquareRoot => TargetJetClassification::Custom(option(Fe)),
        /*
         * Digital signatures
         */
        Elements::CheckSigVerify | Elements::Bip0340Verify => TargetJetClassification::Unary,
        /*
         * Bitcoin (without primitives)
         */
        Elements::ParseLock => TargetJetClassification::Custom(either(Height, Time)),
        Elements::ParseSequence => {
            TargetJetClassification::Custom(option(either(Distance, Duration)))
        }
        Elements::TapdataInit => TargetJetClassification::Custom(Ctx8.into()),
        /*
         * ==============================
         *         Elements jets
         * ==============================
         *
         * Signature hash modes
         */
        Elements::SigAllHash
        | Elements::TxHash
        | Elements::TapEnvHash
        | Elements::InputsHash
        | Elements::OutputsHash
        | Elements::IssuancesHash
        | Elements::InputUtxosHash
        | Elements::OutputAmountsHash
        | Elements::OutputScriptsHash
        | Elements::OutputNoncesHash
        | Elements::OutputRangeProofsHash
        | Elements::OutputSurjectionProofsHash
        | Elements::InputOutpointsHash
        | Elements::InputAnnexesHash
        | Elements::InputSequencesHash
        | Elements::InputScriptSigsHash
        | Elements::IssuanceAssetAmountsHash
        | Elements::IssuanceTokenAmountsHash
        | Elements::IssuanceRangeProofsHash
        | Elements::IssuanceBlindingEntropyHash
        | Elements::InputAmountsHash
        | Elements::InputScriptsHash
        | Elements::TapleafHash
        | Elements::TappathHash
        | Elements::BuildTapleafSimplicity
        | Elements::BuildTapbranch
        | Elements::BuildTaptweak => TargetJetClassification::Unary,
        Elements::OutpointHash
        | Elements::AssetAmountHash
        | Elements::NonceHash
        | Elements::AnnexHash => TargetJetClassification::Custom(Ctx8.into()),
        /*
         * Time locks
         */
        Elements::CheckLockTime
        | Elements::BrokenDoNotUseCheckLockDistance
        | Elements::BrokenDoNotUseCheckLockDuration
        | Elements::CheckLockHeight => TargetJetClassification::Unary,
        Elements::TxIsFinal => TargetJetClassification::Custom(bool()),
        Elements::TxLockTime => TargetJetClassification::Custom(Time.into()),
        Elements::BrokenDoNotUseTxLockDistance => TargetJetClassification::Custom(Distance.into()),
        Elements::BrokenDoNotUseTxLockDuration => TargetJetClassification::Custom(Duration.into()),
        Elements::TxLockHeight => TargetJetClassification::Custom(Height.into()),
        /*
         * Issuance
         */
        Elements::Issuance => TargetJetClassification::Custom(option(option(bool()))),
        Elements::IssuanceAsset | Elements::IssuanceToken => {
            TargetJetClassification::Custom(option(option(ExplicitAsset)))
        }
        Elements::IssuanceEntropy => TargetJetClassification::Custom(option(option(U256))),
        Elements::CalculateIssuanceEntropy => TargetJetClassification::Unary,
        Elements::CalculateAsset
        | Elements::CalculateExplicitToken
        | Elements::CalculateConfidentialToken => {
            TargetJetClassification::Custom(ExplicitAsset.into())
        }
        /*
         * Transaction
         */
        Elements::TapleafVersion => TargetJetClassification::Unary,
        Elements::CurrentIndex
        | Elements::NumInputs
        | Elements::NumOutputs
        | Elements::CurrentSequence
        | Elements::Version => TargetJetClassification::Unary,
        Elements::ScriptCMR
        | Elements::CurrentScriptHash
        | Elements::CurrentScriptSigHash
        | Elements::CurrentIssuanceAssetProof
        | Elements::CurrentIssuanceTokenProof
        | Elements::GenesisBlockHash
        | Elements::LbtcAsset
        | Elements::TransactionId => TargetJetClassification::Unary,
        Elements::InternalKey => TargetJetClassification::Custom(Pubkey.into()),
        Elements::LockTime => TargetJetClassification::Custom(Lock.into()),
        Elements::InputSequence => TargetJetClassification::Custom(option(U32)),
        Elements::OutputAsset => TargetJetClassification::Custom(option(Asset1)),
        Elements::OutputAmount => TargetJetClassification::Custom(option(tuple([Asset1, Amount1]))),
        Elements::OutputNonce => TargetJetClassification::Custom(option(option(Nonce))),
        Elements::OutputScriptHash
        | Elements::OutputSurjectionProof
        | Elements::OutputRangeProof
        | Elements::OutputHash
        | Elements::CurrentPegin
        | Elements::CurrentAnnexHash
        | Elements::CurrentNewIssuanceContract
        | Elements::CurrentReissuanceEntropy
        | Elements::InputScriptHash
        | Elements::InputScriptSigHash
        | Elements::InputHash
        | Elements::InputUtxoHash
        | Elements::IssuanceAssetProof
        | Elements::IssuanceTokenProof
        | Elements::IssuanceHash
        | Elements::Tappath => TargetJetClassification::Custom(option(U256)),
        Elements::OutputNullDatum => TargetJetClassification::Custom(option(option(either(
            tuple([U2, U256]),
            either(U1, U4),
        )))),
        Elements::OutputIsFee => TargetJetClassification::Custom(option(bool())),
        Elements::TotalFee => TargetJetClassification::Custom(ExplicitAmount.into()),
        Elements::CurrentPrevOutpoint => TargetJetClassification::Custom(Outpoint.into()),
        Elements::CurrentAsset => TargetJetClassification::Custom(Asset1.into()),
        Elements::CurrentAmount => TargetJetClassification::Custom(tuple([Asset1, Amount1])),
        Elements::CurrentReissuanceBlinding => {
            TargetJetClassification::Custom(option(ExplicitNonce))
        }
        Elements::CurrentIssuanceAssetAmount => TargetJetClassification::Custom(option(Amount1)),
        Elements::CurrentIssuanceTokenAmount => {
            TargetJetClassification::Custom(option(TokenAmount1))
        }
        Elements::InputPegin
        | Elements::InputAnnexHash
        | Elements::NewIssuanceContract
        | Elements::ReissuanceEntropy => TargetJetClassification::Custom(option(option(U256))),
        Elements::InputPrevOutpoint => TargetJetClassification::Custom(option(Outpoint)),
        Elements::InputAsset => TargetJetClassification::Custom(option(Asset1)),
        Elements::InputAmount => TargetJetClassification::Custom(option(tuple([Asset1, Amount1]))),
        Elements::ReissuanceBlinding => {
            TargetJetClassification::Custom(option(option(ExplicitNonce)))
        }
        Elements::IssuanceAssetAmount => TargetJetClassification::Custom(option(option(Amount1))),
        Elements::IssuanceTokenAmount => {
            TargetJetClassification::Custom(option(option(TokenAmount1)))
        }
    }
}
