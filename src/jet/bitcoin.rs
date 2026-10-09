// Adapted from delta1/SimplicityHL@17f0fa4c535c2794df0e79d8c702458d1764a16d, src/jet/bitcoin.rs.
use super::*;
use crate::types::BuiltinAlias::*;
use crate::types::UIntType::*;

use simplicity::jet::{Bitcoin, Jet};

impl JetHL for Bitcoin {
    fn source_jet_classification(&self) -> SourceJetClassification {
        source_jet_classification(*self)
    }

    fn target_jet_classification(&self) -> TargetJetClassification {
        target_jet_classification(*self)
    }

    fn is_disabled(&self) -> bool {
        matches!(self, Bitcoin::CheckSigVerify | Bitcoin::Verify)
    }

    fn clone_box(&self) -> Box<dyn JetHL> {
        Box::new(*self)
    }

    fn as_jet(&self) -> &dyn Jet {
        self
    }
}

fn source_jet_classification(jet: Bitcoin) -> SourceJetClassification {
    match jet {
        Bitcoin::Low1
        | Bitcoin::Low8
        | Bitcoin::Low16
        | Bitcoin::Low32
        | Bitcoin::Low64
        | Bitcoin::High1
        | Bitcoin::High8
        | Bitcoin::High16
        | Bitcoin::High32
        | Bitcoin::High64 => SourceJetClassification::Custom(vec![]),
        Bitcoin::Verify => SourceJetClassification::Custom(vec![bool()]),
        Bitcoin::Complement1
        | Bitcoin::Some1
        | Bitcoin::LeftPadLow1_8
        | Bitcoin::LeftPadLow1_16
        | Bitcoin::LeftPadLow1_32
        | Bitcoin::LeftPadLow1_64
        | Bitcoin::LeftPadHigh1_8
        | Bitcoin::LeftPadHigh1_16
        | Bitcoin::LeftPadHigh1_32
        | Bitcoin::LeftPadHigh1_64
        | Bitcoin::LeftExtend1_8
        | Bitcoin::LeftExtend1_16
        | Bitcoin::LeftExtend1_32
        | Bitcoin::LeftExtend1_64
        | Bitcoin::RightPadLow1_8
        | Bitcoin::RightPadLow1_16
        | Bitcoin::RightPadLow1_32
        | Bitcoin::RightPadLow1_64
        | Bitcoin::RightPadHigh1_8
        | Bitcoin::RightPadHigh1_16
        | Bitcoin::RightPadHigh1_32
        | Bitcoin::RightPadHigh1_64 => SourceJetClassification::Unary,
        Bitcoin::Complement8
        | Bitcoin::Some8
        | Bitcoin::All8
        | Bitcoin::Leftmost8_1
        | Bitcoin::Leftmost8_2
        | Bitcoin::Leftmost8_4
        | Bitcoin::Rightmost8_1
        | Bitcoin::Rightmost8_2
        | Bitcoin::Rightmost8_4
        | Bitcoin::LeftPadLow8_16
        | Bitcoin::LeftPadLow8_32
        | Bitcoin::LeftPadLow8_64
        | Bitcoin::LeftPadHigh8_16
        | Bitcoin::LeftPadHigh8_32
        | Bitcoin::LeftPadHigh8_64
        | Bitcoin::LeftExtend8_16
        | Bitcoin::LeftExtend8_32
        | Bitcoin::LeftExtend8_64
        | Bitcoin::RightPadLow8_16
        | Bitcoin::RightPadLow8_32
        | Bitcoin::RightPadLow8_64
        | Bitcoin::RightPadHigh8_16
        | Bitcoin::RightPadHigh8_32
        | Bitcoin::RightPadHigh8_64
        | Bitcoin::RightExtend8_16
        | Bitcoin::RightExtend8_32
        | Bitcoin::RightExtend8_64 => SourceJetClassification::Unary,
        Bitcoin::Complement16
        | Bitcoin::Some16
        | Bitcoin::All16
        | Bitcoin::Leftmost16_1
        | Bitcoin::Leftmost16_2
        | Bitcoin::Leftmost16_4
        | Bitcoin::Leftmost16_8
        | Bitcoin::Rightmost16_1
        | Bitcoin::Rightmost16_2
        | Bitcoin::Rightmost16_4
        | Bitcoin::Rightmost16_8
        | Bitcoin::LeftPadLow16_32
        | Bitcoin::LeftPadLow16_64
        | Bitcoin::LeftPadHigh16_32
        | Bitcoin::LeftPadHigh16_64
        | Bitcoin::LeftExtend16_32
        | Bitcoin::LeftExtend16_64
        | Bitcoin::RightPadLow16_32
        | Bitcoin::RightPadLow16_64
        | Bitcoin::RightPadHigh16_32
        | Bitcoin::RightPadHigh16_64
        | Bitcoin::RightExtend16_32
        | Bitcoin::RightExtend16_64 => SourceJetClassification::Unary,
        Bitcoin::Complement32
        | Bitcoin::Some32
        | Bitcoin::All32
        | Bitcoin::Leftmost32_1
        | Bitcoin::Leftmost32_2
        | Bitcoin::Leftmost32_4
        | Bitcoin::Leftmost32_8
        | Bitcoin::Leftmost32_16
        | Bitcoin::Rightmost32_1
        | Bitcoin::Rightmost32_2
        | Bitcoin::Rightmost32_4
        | Bitcoin::Rightmost32_8
        | Bitcoin::Rightmost32_16
        | Bitcoin::LeftPadLow32_64
        | Bitcoin::LeftPadHigh32_64
        | Bitcoin::LeftExtend32_64
        | Bitcoin::RightPadLow32_64
        | Bitcoin::RightPadHigh32_64
        | Bitcoin::RightExtend32_64 => SourceJetClassification::Unary,
        Bitcoin::Complement64
        | Bitcoin::Some64
        | Bitcoin::All64
        | Bitcoin::Leftmost64_1
        | Bitcoin::Leftmost64_2
        | Bitcoin::Leftmost64_4
        | Bitcoin::Leftmost64_8
        | Bitcoin::Leftmost64_16
        | Bitcoin::Leftmost64_32
        | Bitcoin::Rightmost64_1
        | Bitcoin::Rightmost64_2
        | Bitcoin::Rightmost64_4
        | Bitcoin::Rightmost64_8
        | Bitcoin::Rightmost64_16
        | Bitcoin::Rightmost64_32 => SourceJetClassification::Unary,
        Bitcoin::And1 | Bitcoin::Or1 | Bitcoin::Xor1 | Bitcoin::Eq1 => {
            SourceJetClassification::Binary
        }
        Bitcoin::And8 | Bitcoin::Or8 | Bitcoin::Xor8 | Bitcoin::Eq8 => {
            SourceJetClassification::Binary
        }
        Bitcoin::And16 | Bitcoin::Or16 | Bitcoin::Xor16 | Bitcoin::Eq16 => {
            SourceJetClassification::Binary
        }
        Bitcoin::And32 | Bitcoin::Or32 | Bitcoin::Xor32 | Bitcoin::Eq32 => {
            SourceJetClassification::Binary
        }
        Bitcoin::And64 | Bitcoin::Or64 | Bitcoin::Xor64 | Bitcoin::Eq64 => {
            SourceJetClassification::Binary
        }
        Bitcoin::Eq256 => SourceJetClassification::Binary,
        Bitcoin::Maj1 | Bitcoin::XorXor1 | Bitcoin::Ch1 => SourceJetClassification::Ternary,
        Bitcoin::Maj8 | Bitcoin::XorXor8 | Bitcoin::Ch8 => SourceJetClassification::Ternary,
        Bitcoin::Maj16 | Bitcoin::XorXor16 | Bitcoin::Ch16 => {
            SourceJetClassification::Custom(vec![U16.into(), tuple([U16, U16])])
        }
        Bitcoin::Maj32 | Bitcoin::XorXor32 | Bitcoin::Ch32 => {
            SourceJetClassification::Custom(vec![U32.into(), tuple([U32, U32])])
        }
        Bitcoin::Maj64 | Bitcoin::XorXor64 | Bitcoin::Ch64 => {
            SourceJetClassification::Custom(vec![U64.into(), tuple([U64, U64])])
        }
        Bitcoin::FullLeftShift8_1 => SourceJetClassification::Custom(vec![U8.into(), U1.into()]),
        Bitcoin::FullLeftShift8_2 => SourceJetClassification::Custom(vec![U8.into(), U2.into()]),
        Bitcoin::FullLeftShift8_4 => SourceJetClassification::Custom(vec![U8.into(), U4.into()]),
        Bitcoin::FullLeftShift16_1 => SourceJetClassification::Custom(vec![U16.into(), U1.into()]),
        Bitcoin::FullLeftShift16_2 => SourceJetClassification::Custom(vec![U16.into(), U2.into()]),
        Bitcoin::FullLeftShift16_4 => SourceJetClassification::Custom(vec![U16.into(), U4.into()]),
        Bitcoin::FullLeftShift16_8 => SourceJetClassification::Custom(vec![U16.into(), U8.into()]),
        Bitcoin::FullLeftShift32_1 => SourceJetClassification::Custom(vec![U32.into(), U1.into()]),
        Bitcoin::FullLeftShift32_2 => SourceJetClassification::Custom(vec![U32.into(), U2.into()]),
        Bitcoin::FullLeftShift32_4 => SourceJetClassification::Custom(vec![U32.into(), U4.into()]),
        Bitcoin::FullLeftShift32_8 => SourceJetClassification::Custom(vec![U32.into(), U8.into()]),
        Bitcoin::FullLeftShift32_16 => {
            SourceJetClassification::Custom(vec![U32.into(), U16.into()])
        }
        Bitcoin::FullLeftShift64_1 => SourceJetClassification::Custom(vec![U64.into(), U1.into()]),
        Bitcoin::FullLeftShift64_2 => SourceJetClassification::Custom(vec![U64.into(), U2.into()]),
        Bitcoin::FullLeftShift64_4 => SourceJetClassification::Custom(vec![U64.into(), U4.into()]),
        Bitcoin::FullLeftShift64_8 => SourceJetClassification::Custom(vec![U64.into(), U8.into()]),
        Bitcoin::FullLeftShift64_16 => {
            SourceJetClassification::Custom(vec![U64.into(), U16.into()])
        }
        Bitcoin::FullLeftShift64_32 => {
            SourceJetClassification::Custom(vec![U64.into(), U32.into()])
        }
        Bitcoin::FullRightShift8_1 => SourceJetClassification::Custom(vec![U1.into(), U8.into()]),
        Bitcoin::FullRightShift8_2 => SourceJetClassification::Custom(vec![U2.into(), U8.into()]),
        Bitcoin::FullRightShift8_4 => SourceJetClassification::Custom(vec![U4.into(), U8.into()]),
        Bitcoin::FullRightShift16_1 => SourceJetClassification::Custom(vec![U1.into(), U16.into()]),
        Bitcoin::FullRightShift16_2 => SourceJetClassification::Custom(vec![U2.into(), U16.into()]),
        Bitcoin::FullRightShift16_4 => SourceJetClassification::Custom(vec![U4.into(), U16.into()]),
        Bitcoin::FullRightShift16_8 => SourceJetClassification::Custom(vec![U8.into(), U16.into()]),
        Bitcoin::FullRightShift32_1 => SourceJetClassification::Custom(vec![U1.into(), U32.into()]),
        Bitcoin::FullRightShift32_2 => SourceJetClassification::Custom(vec![U2.into(), U32.into()]),
        Bitcoin::FullRightShift32_4 => SourceJetClassification::Custom(vec![U4.into(), U32.into()]),
        Bitcoin::FullRightShift32_8 => SourceJetClassification::Custom(vec![U8.into(), U32.into()]),
        Bitcoin::FullRightShift32_16 => {
            SourceJetClassification::Custom(vec![U16.into(), U32.into()])
        }
        Bitcoin::FullRightShift64_1 => SourceJetClassification::Custom(vec![U1.into(), U64.into()]),
        Bitcoin::FullRightShift64_2 => SourceJetClassification::Custom(vec![U2.into(), U64.into()]),
        Bitcoin::FullRightShift64_4 => SourceJetClassification::Custom(vec![U4.into(), U64.into()]),
        Bitcoin::FullRightShift64_8 => SourceJetClassification::Custom(vec![U8.into(), U64.into()]),
        Bitcoin::FullRightShift64_16 => {
            SourceJetClassification::Custom(vec![U16.into(), U64.into()])
        }
        Bitcoin::FullRightShift64_32 => {
            SourceJetClassification::Custom(vec![U32.into(), U64.into()])
        }
        Bitcoin::LeftShiftWith8 | Bitcoin::RightShiftWith8 => {
            SourceJetClassification::Custom(vec![U1.into(), U4.into(), U8.into()])
        }
        Bitcoin::LeftShiftWith16 | Bitcoin::RightShiftWith16 => {
            SourceJetClassification::Custom(vec![U1.into(), U4.into(), U16.into()])
        }
        Bitcoin::LeftShiftWith32 | Bitcoin::RightShiftWith32 => {
            SourceJetClassification::Custom(vec![U1.into(), U8.into(), U32.into()])
        }
        Bitcoin::LeftShiftWith64 | Bitcoin::RightShiftWith64 => {
            SourceJetClassification::Custom(vec![U1.into(), U8.into(), U64.into()])
        }
        Bitcoin::LeftShift8
        | Bitcoin::RightShift8
        | Bitcoin::LeftRotate8
        | Bitcoin::RightRotate8 => SourceJetClassification::Custom(vec![U4.into(), U8.into()]),
        Bitcoin::LeftShift16
        | Bitcoin::RightShift16
        | Bitcoin::LeftRotate16
        | Bitcoin::RightRotate16 => SourceJetClassification::Custom(vec![U4.into(), U16.into()]),
        Bitcoin::LeftShift32
        | Bitcoin::RightShift32
        | Bitcoin::LeftRotate32
        | Bitcoin::RightRotate32 => SourceJetClassification::Custom(vec![U8.into(), U32.into()]),
        Bitcoin::LeftShift64
        | Bitcoin::RightShift64
        | Bitcoin::LeftRotate64
        | Bitcoin::RightRotate64 => SourceJetClassification::Custom(vec![U8.into(), U64.into()]),
        Bitcoin::One8 | Bitcoin::One16 | Bitcoin::One32 | Bitcoin::One64 => {
            SourceJetClassification::Custom(vec![])
        }
        Bitcoin::Increment8
        | Bitcoin::Negate8
        | Bitcoin::Decrement8
        | Bitcoin::IsZero8
        | Bitcoin::IsOne8 => SourceJetClassification::Unary,
        Bitcoin::Increment16
        | Bitcoin::Negate16
        | Bitcoin::Decrement16
        | Bitcoin::IsZero16
        | Bitcoin::IsOne16 => SourceJetClassification::Unary,
        Bitcoin::Increment32
        | Bitcoin::Negate32
        | Bitcoin::Decrement32
        | Bitcoin::IsZero32
        | Bitcoin::IsOne32 => SourceJetClassification::Unary,
        Bitcoin::Increment64
        | Bitcoin::Negate64
        | Bitcoin::Decrement64
        | Bitcoin::IsZero64
        | Bitcoin::IsOne64 => SourceJetClassification::Unary,
        Bitcoin::Add8
        | Bitcoin::Subtract8
        | Bitcoin::Multiply8
        | Bitcoin::Le8
        | Bitcoin::Lt8
        | Bitcoin::Min8
        | Bitcoin::Max8
        | Bitcoin::DivMod8
        | Bitcoin::Divide8
        | Bitcoin::Modulo8
        | Bitcoin::Divides8 => SourceJetClassification::Binary,
        Bitcoin::Add16
        | Bitcoin::Subtract16
        | Bitcoin::Multiply16
        | Bitcoin::Le16
        | Bitcoin::Lt16
        | Bitcoin::Min16
        | Bitcoin::Max16
        | Bitcoin::DivMod16
        | Bitcoin::Divide16
        | Bitcoin::Modulo16
        | Bitcoin::Divides16 => SourceJetClassification::Binary,
        Bitcoin::Add32
        | Bitcoin::Subtract32
        | Bitcoin::Multiply32
        | Bitcoin::Le32
        | Bitcoin::Lt32
        | Bitcoin::Min32
        | Bitcoin::Max32
        | Bitcoin::DivMod32
        | Bitcoin::Divide32
        | Bitcoin::Modulo32
        | Bitcoin::Divides32 => SourceJetClassification::Binary,
        Bitcoin::Add64
        | Bitcoin::Subtract64
        | Bitcoin::Multiply64
        | Bitcoin::Le64
        | Bitcoin::Lt64
        | Bitcoin::Min64
        | Bitcoin::Max64
        | Bitcoin::DivMod64
        | Bitcoin::Divide64
        | Bitcoin::Modulo64
        | Bitcoin::Divides64 => SourceJetClassification::Binary,
        Bitcoin::DivMod128_64 => SourceJetClassification::Custom(vec![U128.into(), U64.into()]),
        Bitcoin::FullAdd8 | Bitcoin::FullSubtract8 => {
            SourceJetClassification::Custom(vec![bool(), U8.into(), U8.into()])
        }
        Bitcoin::FullAdd16 | Bitcoin::FullSubtract16 => {
            SourceJetClassification::Custom(vec![bool(), U16.into(), U16.into()])
        }
        Bitcoin::FullAdd32 | Bitcoin::FullSubtract32 => {
            SourceJetClassification::Custom(vec![bool(), U32.into(), U32.into()])
        }
        Bitcoin::FullAdd64 | Bitcoin::FullSubtract64 => {
            SourceJetClassification::Custom(vec![bool(), U64.into(), U64.into()])
        }
        Bitcoin::FullIncrement8 | Bitcoin::FullDecrement8 => {
            SourceJetClassification::Custom(vec![bool(), U8.into()])
        }
        Bitcoin::FullIncrement16 | Bitcoin::FullDecrement16 => {
            SourceJetClassification::Custom(vec![bool(), U16.into()])
        }
        Bitcoin::FullIncrement32 | Bitcoin::FullDecrement32 => {
            SourceJetClassification::Custom(vec![bool(), U32.into()])
        }
        Bitcoin::FullIncrement64 | Bitcoin::FullDecrement64 => {
            SourceJetClassification::Custom(vec![bool(), U64.into()])
        }
        Bitcoin::FullMultiply8 => SourceJetClassification::Quaternary,
        Bitcoin::FullMultiply16 => SourceJetClassification::Quaternary,
        Bitcoin::FullMultiply32 => SourceJetClassification::Quaternary,
        Bitcoin::FullMultiply64 => SourceJetClassification::Quaternary,
        Bitcoin::Median8 => SourceJetClassification::Ternary,
        Bitcoin::Median16 => SourceJetClassification::Ternary,
        Bitcoin::Median32 => SourceJetClassification::Ternary,
        Bitcoin::Median64 => SourceJetClassification::Ternary,
        Bitcoin::Sha256Iv | Bitcoin::Sha256Ctx8Init => SourceJetClassification::Custom(vec![]),
        Bitcoin::Sha256Block => SourceJetClassification::Ternary,
        Bitcoin::Sha256Ctx8Add1 => SourceJetClassification::Custom(vec![Ctx8.into(), U8.into()]),
        Bitcoin::Sha256Ctx8Add2 => SourceJetClassification::Custom(vec![Ctx8.into(), U16.into()]),
        Bitcoin::Sha256Ctx8Add4 => SourceJetClassification::Custom(vec![Ctx8.into(), U32.into()]),
        Bitcoin::Sha256Ctx8Add8 => SourceJetClassification::Custom(vec![Ctx8.into(), U64.into()]),
        Bitcoin::Sha256Ctx8Add16 => SourceJetClassification::Custom(vec![Ctx8.into(), U128.into()]),
        Bitcoin::Sha256Ctx8Add32 => SourceJetClassification::Custom(vec![Ctx8.into(), U256.into()]),
        Bitcoin::Sha256Ctx8Add64 => {
            SourceJetClassification::Custom(vec![Ctx8.into(), array(U8, 64)])
        }
        Bitcoin::Sha256Ctx8Add128 => {
            SourceJetClassification::Custom(vec![Ctx8.into(), array(U8, 128)])
        }
        Bitcoin::Sha256Ctx8Add256 => {
            SourceJetClassification::Custom(vec![Ctx8.into(), array(U8, 256)])
        }
        Bitcoin::Sha256Ctx8Add512 => {
            SourceJetClassification::Custom(vec![Ctx8.into(), array(U8, 512)])
        }
        Bitcoin::Sha256Ctx8AddBuffer511 => {
            SourceJetClassification::Custom(vec![Ctx8.into(), list(U8, 512)])
        }
        Bitcoin::Sha256Ctx8Finalize => SourceJetClassification::Custom(vec![Ctx8.into()]),
        Bitcoin::PointVerify1 => SourceJetClassification::Custom(vec![
            tuple([tuple([Scalar, Point]), Scalar.into()]),
            Point.into(),
        ]),
        Bitcoin::Decompress => SourceJetClassification::Custom(vec![Point.into()]),
        Bitcoin::LinearVerify1 => SourceJetClassification::Custom(vec![
            tuple([tuple([Scalar, Ge]), Scalar.into()]),
            Ge.into(),
        ]),
        Bitcoin::LinearCombination1 => {
            SourceJetClassification::Custom(vec![tuple([Scalar, Gej]), Scalar.into()])
        }
        Bitcoin::Scale => SourceJetClassification::Custom(vec![Scalar.into(), Gej.into()]),
        Bitcoin::Generate => SourceJetClassification::Custom(vec![Scalar.into()]),
        Bitcoin::GejInfinity => SourceJetClassification::Custom(vec![]),
        Bitcoin::GejNormalize
        | Bitcoin::GejNegate
        | Bitcoin::GejDouble
        | Bitcoin::GejIsInfinity
        | Bitcoin::GejYIsOdd
        | Bitcoin::GejIsOnCurve => SourceJetClassification::Custom(vec![Gej.into()]),
        Bitcoin::GeNegate | Bitcoin::GeIsOnCurve => {
            SourceJetClassification::Custom(vec![Ge.into()])
        }
        Bitcoin::GejAdd | Bitcoin::GejEquiv => {
            SourceJetClassification::Custom(vec![Gej.into(), Gej.into()])
        }
        Bitcoin::GejGeAddEx | Bitcoin::GejGeAdd | Bitcoin::GejGeEquiv => {
            SourceJetClassification::Custom(vec![Gej.into(), Ge.into()])
        }
        Bitcoin::GejRescale => SourceJetClassification::Custom(vec![Gej.into(), Fe.into()]),
        Bitcoin::GejXEquiv => SourceJetClassification::Custom(vec![Fe.into(), Gej.into()]),
        Bitcoin::ScalarAdd | Bitcoin::ScalarMultiply => {
            SourceJetClassification::Custom(vec![Scalar.into(), Scalar.into()])
        }
        Bitcoin::ScalarNormalize
        | Bitcoin::ScalarNegate
        | Bitcoin::ScalarSquare
        | Bitcoin::ScalarInvert
        | Bitcoin::ScalarMultiplyLambda
        | Bitcoin::ScalarIsZero => SourceJetClassification::Custom(vec![Scalar.into()]),
        Bitcoin::FeNormalize
        | Bitcoin::FeNegate
        | Bitcoin::FeSquare
        | Bitcoin::FeMultiplyBeta
        | Bitcoin::FeInvert
        | Bitcoin::FeSquareRoot
        | Bitcoin::FeIsZero
        | Bitcoin::FeIsOdd
        | Bitcoin::Swu => SourceJetClassification::Custom(vec![Fe.into()]),
        Bitcoin::FeAdd | Bitcoin::FeMultiply => {
            SourceJetClassification::Custom(vec![Fe.into(), Fe.into()])
        }
        Bitcoin::HashToCurve => SourceJetClassification::Unary,
        Bitcoin::CheckSigVerify => {
            SourceJetClassification::Custom(vec![tuple([Pubkey, Message64]), Signature.into()])
        }
        Bitcoin::Bip0340Verify => {
            SourceJetClassification::Custom(vec![tuple([Pubkey, Message]), Signature.into()])
        }
        Bitcoin::TapdataInit => SourceJetClassification::Custom(vec![]),
        Bitcoin::ParseLock | Bitcoin::ParseSequence => SourceJetClassification::Unary,
        Bitcoin::SigAllHash
        | Bitcoin::TxHash
        | Bitcoin::TapEnvHash
        | Bitcoin::InputsHash
        | Bitcoin::OutputsHash
        | Bitcoin::InputUtxosHash
        | Bitcoin::OutputScriptsHash
        | Bitcoin::InputOutpointsHash
        | Bitcoin::InputAnnexesHash
        | Bitcoin::InputSequencesHash
        | Bitcoin::InputScriptSigsHash
        | Bitcoin::InputScriptsHash
        | Bitcoin::TapleafHash
        | Bitcoin::TappathHash
        | Bitcoin::InputValuesHash
        | Bitcoin::OutputValuesHash => SourceJetClassification::Custom(vec![]),
        Bitcoin::OutpointHash => {
            SourceJetClassification::Custom(vec![Ctx8.into(), Outpoint.into()])
        }
        Bitcoin::AnnexHash => SourceJetClassification::Custom(vec![Ctx8.into(), option(U256)]),
        Bitcoin::BuildTapleafSimplicity => SourceJetClassification::Unary,
        Bitcoin::BuildTapbranch => SourceJetClassification::Binary,
        Bitcoin::BuildTaptweak => SourceJetClassification::Custom(vec![Pubkey.into(), U256.into()]),
        Bitcoin::CheckLockTime => SourceJetClassification::Custom(vec![Time.into()]),
        Bitcoin::CheckLockHeight => SourceJetClassification::Custom(vec![Height.into()]),
        Bitcoin::CheckLockDistance => SourceJetClassification::Custom(vec![Distance.into()]),
        Bitcoin::CheckLockDuration => SourceJetClassification::Custom(vec![Duration.into()]),
        Bitcoin::TxLockTime
        | Bitcoin::TxLockHeight
        | Bitcoin::TxLockDistance
        | Bitcoin::TxLockDuration
        | Bitcoin::TxIsFinal => SourceJetClassification::Custom(vec![]),
        Bitcoin::ScriptCMR
        | Bitcoin::InternalKey
        | Bitcoin::CurrentIndex
        | Bitcoin::NumInputs
        | Bitcoin::NumOutputs
        | Bitcoin::LockTime
        | Bitcoin::CurrentPrevOutpoint
        | Bitcoin::CurrentScriptHash
        | Bitcoin::CurrentSequence
        | Bitcoin::CurrentAnnexHash
        | Bitcoin::CurrentScriptSigHash
        | Bitcoin::CurrentValue
        | Bitcoin::TapleafVersion
        | Bitcoin::Version
        | Bitcoin::TransactionId
        | Bitcoin::TotalInputValue
        | Bitcoin::TotalOutputValue
        | Bitcoin::Fee => SourceJetClassification::Custom(vec![]),
        Bitcoin::OutputScriptHash
        | Bitcoin::OutputHash
        | Bitcoin::OutputValue
        | Bitcoin::InputPrevOutpoint
        | Bitcoin::InputScriptHash
        | Bitcoin::InputSequence
        | Bitcoin::InputAnnexHash
        | Bitcoin::InputScriptSigHash
        | Bitcoin::InputHash
        | Bitcoin::InputUtxoHash
        | Bitcoin::InputValue => SourceJetClassification::Unary,
        Bitcoin::Tappath => SourceJetClassification::Unary,
    }
}

fn target_jet_classification(jet: Bitcoin) -> TargetJetClassification {
    match jet {
        /*
         * ==============================
         *          Core jets
         * ==============================
         *
         * Multi-bit logic
         */
        Bitcoin::Verify => TargetJetClassification::Custom(AliasedType::unit()),
        Bitcoin::Some1
        | Bitcoin::Some8
        | Bitcoin::Some16
        | Bitcoin::Some32
        | Bitcoin::Some64
        | Bitcoin::All8
        | Bitcoin::All16
        | Bitcoin::All32
        | Bitcoin::All64
        | Bitcoin::Eq1
        | Bitcoin::Eq8
        | Bitcoin::Eq16
        | Bitcoin::Eq32
        | Bitcoin::Eq64
        | Bitcoin::Eq256 => TargetJetClassification::Custom(bool()),
        Bitcoin::Low1
        | Bitcoin::High1
        | Bitcoin::Complement1
        | Bitcoin::And1
        | Bitcoin::Or1
        | Bitcoin::Xor1
        | Bitcoin::Maj1
        | Bitcoin::XorXor1
        | Bitcoin::Ch1
        | Bitcoin::Leftmost8_1
        | Bitcoin::Rightmost8_1
        | Bitcoin::Leftmost16_1
        | Bitcoin::Rightmost16_1
        | Bitcoin::Leftmost32_1
        | Bitcoin::Rightmost32_1
        | Bitcoin::Leftmost64_1
        | Bitcoin::Rightmost64_1 => TargetJetClassification::Custom(U1.into()),
        Bitcoin::Leftmost8_2
        | Bitcoin::Rightmost8_2
        | Bitcoin::Leftmost16_2
        | Bitcoin::Rightmost16_2
        | Bitcoin::Leftmost32_2
        | Bitcoin::Rightmost32_2
        | Bitcoin::Leftmost64_2
        | Bitcoin::Rightmost64_2 => TargetJetClassification::Custom(U2.into()),
        Bitcoin::Leftmost8_4
        | Bitcoin::Rightmost8_4
        | Bitcoin::Leftmost16_4
        | Bitcoin::Rightmost16_4
        | Bitcoin::Leftmost32_4
        | Bitcoin::Rightmost32_4
        | Bitcoin::Leftmost64_4
        | Bitcoin::Rightmost64_4 => TargetJetClassification::Custom(U4.into()),
        Bitcoin::Low8
        | Bitcoin::High8
        | Bitcoin::Complement8
        | Bitcoin::And8
        | Bitcoin::Or8
        | Bitcoin::Xor8
        | Bitcoin::Maj8
        | Bitcoin::XorXor8
        | Bitcoin::Ch8
        | Bitcoin::Leftmost16_8
        | Bitcoin::Rightmost16_8
        | Bitcoin::Leftmost32_8
        | Bitcoin::Rightmost32_8
        | Bitcoin::Leftmost64_8
        | Bitcoin::Rightmost64_8
        | Bitcoin::LeftPadLow1_8
        | Bitcoin::LeftPadHigh1_8
        | Bitcoin::LeftExtend1_8
        | Bitcoin::RightPadLow1_8
        | Bitcoin::RightPadHigh1_8
        | Bitcoin::LeftShiftWith8
        | Bitcoin::RightShiftWith8
        | Bitcoin::LeftShift8
        | Bitcoin::RightShift8
        | Bitcoin::LeftRotate8
        | Bitcoin::RightRotate8 => TargetJetClassification::Custom(U8.into()),
        Bitcoin::Low16
        | Bitcoin::High16
        | Bitcoin::Complement16
        | Bitcoin::And16
        | Bitcoin::Or16
        | Bitcoin::Xor16
        | Bitcoin::Maj16
        | Bitcoin::XorXor16
        | Bitcoin::Ch16
        | Bitcoin::Leftmost32_16
        | Bitcoin::Rightmost32_16
        | Bitcoin::Leftmost64_16
        | Bitcoin::Rightmost64_16
        | Bitcoin::LeftPadLow1_16
        | Bitcoin::LeftPadHigh1_16
        | Bitcoin::LeftExtend1_16
        | Bitcoin::RightPadLow1_16
        | Bitcoin::RightPadHigh1_16
        | Bitcoin::LeftPadLow8_16
        | Bitcoin::LeftPadHigh8_16
        | Bitcoin::LeftExtend8_16
        | Bitcoin::RightPadLow8_16
        | Bitcoin::RightPadHigh8_16
        | Bitcoin::RightExtend8_16
        | Bitcoin::LeftShiftWith16
        | Bitcoin::RightShiftWith16
        | Bitcoin::LeftShift16
        | Bitcoin::RightShift16
        | Bitcoin::LeftRotate16
        | Bitcoin::RightRotate16 => TargetJetClassification::Custom(U16.into()),
        Bitcoin::Low32
        | Bitcoin::High32
        | Bitcoin::Complement32
        | Bitcoin::And32
        | Bitcoin::Or32
        | Bitcoin::Xor32
        | Bitcoin::Maj32
        | Bitcoin::XorXor32
        | Bitcoin::Ch32
        | Bitcoin::Leftmost64_32
        | Bitcoin::Rightmost64_32
        | Bitcoin::LeftPadLow1_32
        | Bitcoin::LeftPadHigh1_32
        | Bitcoin::LeftExtend1_32
        | Bitcoin::RightPadLow1_32
        | Bitcoin::RightPadHigh1_32
        | Bitcoin::LeftPadLow8_32
        | Bitcoin::LeftPadHigh8_32
        | Bitcoin::LeftExtend8_32
        | Bitcoin::RightPadLow8_32
        | Bitcoin::RightPadHigh8_32
        | Bitcoin::RightExtend8_32
        | Bitcoin::LeftPadLow16_32
        | Bitcoin::LeftPadHigh16_32
        | Bitcoin::LeftExtend16_32
        | Bitcoin::RightPadLow16_32
        | Bitcoin::RightPadHigh16_32
        | Bitcoin::RightExtend16_32
        | Bitcoin::LeftShiftWith32
        | Bitcoin::RightShiftWith32
        | Bitcoin::LeftShift32
        | Bitcoin::RightShift32
        | Bitcoin::LeftRotate32
        | Bitcoin::RightRotate32 => TargetJetClassification::Custom(U32.into()),
        Bitcoin::Low64
        | Bitcoin::High64
        | Bitcoin::Complement64
        | Bitcoin::And64
        | Bitcoin::Or64
        | Bitcoin::Xor64
        | Bitcoin::Maj64
        | Bitcoin::XorXor64
        | Bitcoin::Ch64
        | Bitcoin::LeftPadLow1_64
        | Bitcoin::LeftPadHigh1_64
        | Bitcoin::LeftExtend1_64
        | Bitcoin::RightPadLow1_64
        | Bitcoin::RightPadHigh1_64
        | Bitcoin::LeftPadLow8_64
        | Bitcoin::LeftPadHigh8_64
        | Bitcoin::LeftExtend8_64
        | Bitcoin::RightPadLow8_64
        | Bitcoin::RightPadHigh8_64
        | Bitcoin::RightExtend8_64
        | Bitcoin::LeftPadLow16_64
        | Bitcoin::LeftPadHigh16_64
        | Bitcoin::LeftExtend16_64
        | Bitcoin::RightPadLow16_64
        | Bitcoin::RightPadHigh16_64
        | Bitcoin::RightExtend16_64
        | Bitcoin::LeftPadLow32_64
        | Bitcoin::LeftPadHigh32_64
        | Bitcoin::LeftExtend32_64
        | Bitcoin::RightPadLow32_64
        | Bitcoin::RightPadHigh32_64
        | Bitcoin::RightExtend32_64
        | Bitcoin::LeftShiftWith64
        | Bitcoin::RightShiftWith64
        | Bitcoin::LeftShift64
        | Bitcoin::RightShift64
        | Bitcoin::LeftRotate64
        | Bitcoin::RightRotate64 => TargetJetClassification::Custom(U64.into()),
        Bitcoin::FullLeftShift8_1 => TargetJetClassification::Custom(tuple([U1, U8])),
        Bitcoin::FullLeftShift8_2 => TargetJetClassification::Custom(tuple([U2, U8])),
        Bitcoin::FullLeftShift8_4 => TargetJetClassification::Custom(tuple([U4, U8])),
        Bitcoin::FullLeftShift16_1 => TargetJetClassification::Custom(tuple([U1, U16])),
        Bitcoin::FullLeftShift16_2 => TargetJetClassification::Custom(tuple([U2, U16])),
        Bitcoin::FullLeftShift16_4 => TargetJetClassification::Custom(tuple([U4, U16])),
        Bitcoin::FullLeftShift16_8 => TargetJetClassification::Custom(tuple([U8, U16])),
        Bitcoin::FullLeftShift32_1 => TargetJetClassification::Custom(tuple([U1, U32])),
        Bitcoin::FullLeftShift32_2 => TargetJetClassification::Custom(tuple([U2, U32])),
        Bitcoin::FullLeftShift32_4 => TargetJetClassification::Custom(tuple([U4, U32])),
        Bitcoin::FullLeftShift32_8 => TargetJetClassification::Custom(tuple([U8, U32])),
        Bitcoin::FullLeftShift32_16 => TargetJetClassification::Custom(tuple([U16, U32])),
        Bitcoin::FullLeftShift64_1 => TargetJetClassification::Custom(tuple([U1, U64])),
        Bitcoin::FullLeftShift64_2 => TargetJetClassification::Custom(tuple([U2, U64])),
        Bitcoin::FullLeftShift64_4 => TargetJetClassification::Custom(tuple([U4, U64])),
        Bitcoin::FullLeftShift64_8 => TargetJetClassification::Custom(tuple([U8, U64])),
        Bitcoin::FullLeftShift64_16 => TargetJetClassification::Custom(tuple([U16, U64])),
        Bitcoin::FullLeftShift64_32 => TargetJetClassification::Custom(tuple([U32, U64])),
        Bitcoin::FullRightShift8_1 => TargetJetClassification::Custom(tuple([U8, U1])),
        Bitcoin::FullRightShift8_2 => TargetJetClassification::Custom(tuple([U8, U2])),
        Bitcoin::FullRightShift8_4 => TargetJetClassification::Custom(tuple([U8, U4])),
        Bitcoin::FullRightShift16_1 => TargetJetClassification::Custom(tuple([U16, U1])),
        Bitcoin::FullRightShift16_2 => TargetJetClassification::Custom(tuple([U16, U2])),
        Bitcoin::FullRightShift16_4 => TargetJetClassification::Custom(tuple([U16, U4])),
        Bitcoin::FullRightShift16_8 => TargetJetClassification::Custom(tuple([U16, U8])),
        Bitcoin::FullRightShift32_1 => TargetJetClassification::Custom(tuple([U32, U1])),
        Bitcoin::FullRightShift32_2 => TargetJetClassification::Custom(tuple([U32, U2])),
        Bitcoin::FullRightShift32_4 => TargetJetClassification::Custom(tuple([U32, U4])),
        Bitcoin::FullRightShift32_8 => TargetJetClassification::Custom(tuple([U32, U8])),
        Bitcoin::FullRightShift32_16 => TargetJetClassification::Custom(tuple([U32, U16])),
        Bitcoin::FullRightShift64_1 => TargetJetClassification::Custom(tuple([U64, U1])),
        Bitcoin::FullRightShift64_2 => TargetJetClassification::Custom(tuple([U64, U2])),
        Bitcoin::FullRightShift64_4 => TargetJetClassification::Custom(tuple([U64, U4])),
        Bitcoin::FullRightShift64_8 => TargetJetClassification::Custom(tuple([U64, U8])),
        Bitcoin::FullRightShift64_16 => TargetJetClassification::Custom(tuple([U64, U16])),
        Bitcoin::FullRightShift64_32 => TargetJetClassification::Custom(tuple([U64, U32])),
        /*
         * Arithmetic
         */
        Bitcoin::Le8
        | Bitcoin::Lt8
        | Bitcoin::Le16
        | Bitcoin::Lt16
        | Bitcoin::Le32
        | Bitcoin::Lt32
        | Bitcoin::Le64
        | Bitcoin::Lt64
        | Bitcoin::IsZero8
        | Bitcoin::IsOne8
        | Bitcoin::IsZero16
        | Bitcoin::IsOne16
        | Bitcoin::IsZero32
        | Bitcoin::IsOne32
        | Bitcoin::IsZero64
        | Bitcoin::IsOne64
        | Bitcoin::Divides8
        | Bitcoin::Divides16
        | Bitcoin::Divides32
        | Bitcoin::Divides64 => TargetJetClassification::Custom(bool()),
        Bitcoin::One8
        | Bitcoin::Min8
        | Bitcoin::Max8
        | Bitcoin::Divide8
        | Bitcoin::Modulo8
        | Bitcoin::Median8 => TargetJetClassification::Custom(U8.into()),
        Bitcoin::One16
        | Bitcoin::Min16
        | Bitcoin::Max16
        | Bitcoin::Divide16
        | Bitcoin::Modulo16
        | Bitcoin::Multiply8
        | Bitcoin::FullMultiply8
        | Bitcoin::Median16 => TargetJetClassification::Custom(U16.into()),
        Bitcoin::One32
        | Bitcoin::Min32
        | Bitcoin::Max32
        | Bitcoin::Divide32
        | Bitcoin::Modulo32
        | Bitcoin::Multiply16
        | Bitcoin::FullMultiply16
        | Bitcoin::Median32 => TargetJetClassification::Custom(U32.into()),
        Bitcoin::One64
        | Bitcoin::Min64
        | Bitcoin::Max64
        | Bitcoin::Divide64
        | Bitcoin::Modulo64
        | Bitcoin::Multiply32
        | Bitcoin::FullMultiply32
        | Bitcoin::Median64 => TargetJetClassification::Custom(U64.into()),
        Bitcoin::Multiply64 | Bitcoin::FullMultiply64 => {
            TargetJetClassification::Custom(U128.into())
        }
        Bitcoin::Increment8
        | Bitcoin::Negate8
        | Bitcoin::Decrement8
        | Bitcoin::Add8
        | Bitcoin::Subtract8
        | Bitcoin::FullAdd8
        | Bitcoin::FullSubtract8
        | Bitcoin::FullIncrement8
        | Bitcoin::FullDecrement8 => TargetJetClassification::Custom(tuple([bool(), U8.into()])),
        Bitcoin::Increment16
        | Bitcoin::Negate16
        | Bitcoin::Decrement16
        | Bitcoin::Add16
        | Bitcoin::Subtract16
        | Bitcoin::FullAdd16
        | Bitcoin::FullSubtract16
        | Bitcoin::FullIncrement16
        | Bitcoin::FullDecrement16 => TargetJetClassification::Custom(tuple([bool(), U16.into()])),
        Bitcoin::Increment32
        | Bitcoin::Negate32
        | Bitcoin::Decrement32
        | Bitcoin::Add32
        | Bitcoin::Subtract32
        | Bitcoin::FullAdd32
        | Bitcoin::FullSubtract32
        | Bitcoin::FullIncrement32
        | Bitcoin::FullDecrement32 => TargetJetClassification::Custom(tuple([bool(), U32.into()])),
        Bitcoin::Increment64
        | Bitcoin::Negate64
        | Bitcoin::Decrement64
        | Bitcoin::Add64
        | Bitcoin::Subtract64
        | Bitcoin::FullAdd64
        | Bitcoin::FullSubtract64
        | Bitcoin::FullIncrement64
        | Bitcoin::FullDecrement64 => TargetJetClassification::Custom(tuple([bool(), U64.into()])),
        Bitcoin::DivMod8 => TargetJetClassification::Custom(tuple([U8, U8])),
        Bitcoin::DivMod16 => TargetJetClassification::Custom(tuple([U16, U16])),
        Bitcoin::DivMod32 => TargetJetClassification::Custom(tuple([U32, U32])),
        Bitcoin::DivMod64 => TargetJetClassification::Custom(tuple([U64, U64])),
        Bitcoin::DivMod128_64 => TargetJetClassification::Custom(tuple([U64, U64])),
        /*
         * Hash functions
         */
        Bitcoin::Sha256Iv | Bitcoin::Sha256Block | Bitcoin::Sha256Ctx8Finalize => {
            TargetJetClassification::Custom(U256.into())
        }
        Bitcoin::Sha256Ctx8Init
        | Bitcoin::Sha256Ctx8Add1
        | Bitcoin::Sha256Ctx8Add2
        | Bitcoin::Sha256Ctx8Add4
        | Bitcoin::Sha256Ctx8Add8
        | Bitcoin::Sha256Ctx8Add16
        | Bitcoin::Sha256Ctx8Add32
        | Bitcoin::Sha256Ctx8Add64
        | Bitcoin::Sha256Ctx8Add128
        | Bitcoin::Sha256Ctx8Add256
        | Bitcoin::Sha256Ctx8Add512
        | Bitcoin::Sha256Ctx8AddBuffer511 => TargetJetClassification::Custom(Ctx8.into()),
        /*
         * Elliptic curve functions
         */
        Bitcoin::PointVerify1 | Bitcoin::LinearVerify1 => {
            TargetJetClassification::Custom(AliasedType::unit())
        }
        Bitcoin::GejIsInfinity
        | Bitcoin::GejEquiv
        | Bitcoin::GejGeEquiv
        | Bitcoin::GejXEquiv
        | Bitcoin::GejYIsOdd
        | Bitcoin::GejIsOnCurve
        | Bitcoin::GeIsOnCurve
        | Bitcoin::ScalarIsZero
        | Bitcoin::FeIsZero
        | Bitcoin::FeIsOdd => TargetJetClassification::Custom(bool()),
        Bitcoin::GeNegate | Bitcoin::HashToCurve | Bitcoin::Swu => {
            TargetJetClassification::Custom(Ge.into())
        }
        Bitcoin::Decompress | Bitcoin::GejNormalize => TargetJetClassification::Custom(option(Ge)),
        Bitcoin::LinearCombination1
        | Bitcoin::Scale
        | Bitcoin::Generate
        | Bitcoin::GejInfinity
        | Bitcoin::GejNegate
        | Bitcoin::GejDouble
        | Bitcoin::GejAdd
        | Bitcoin::GejGeAdd
        | Bitcoin::GejRescale => TargetJetClassification::Custom(Gej.into()),
        Bitcoin::GejGeAddEx => TargetJetClassification::Custom(tuple([Fe, Gej])),
        Bitcoin::ScalarNormalize
        | Bitcoin::ScalarNegate
        | Bitcoin::ScalarAdd
        | Bitcoin::ScalarSquare
        | Bitcoin::ScalarMultiply
        | Bitcoin::ScalarMultiplyLambda
        | Bitcoin::ScalarInvert => TargetJetClassification::Custom(Scalar.into()),
        Bitcoin::FeNormalize
        | Bitcoin::FeNegate
        | Bitcoin::FeAdd
        | Bitcoin::FeSquare
        | Bitcoin::FeMultiply
        | Bitcoin::FeMultiplyBeta
        | Bitcoin::FeInvert => TargetJetClassification::Custom(Fe.into()),
        Bitcoin::FeSquareRoot => TargetJetClassification::Custom(option(Fe)),
        /*
         * Digital signatures
         */
        Bitcoin::CheckSigVerify | Bitcoin::Bip0340Verify => {
            TargetJetClassification::Custom(AliasedType::unit())
        }
        /*
         * Bitcoin (without primitives)
         */
        Bitcoin::ParseLock => TargetJetClassification::Custom(either(Height, Time)),
        Bitcoin::ParseSequence => {
            TargetJetClassification::Custom(option(either(Distance, Duration)))
        }
        Bitcoin::TapdataInit => TargetJetClassification::Custom(Ctx8.into()),
        /*
         * ==============================
         *         Bitcoin jets
         * ==============================
         *
         * Signature hash modes
         */
        Bitcoin::SigAllHash
        | Bitcoin::TxHash
        | Bitcoin::TapEnvHash
        | Bitcoin::InputsHash
        | Bitcoin::OutputsHash
        | Bitcoin::InputUtxosHash
        | Bitcoin::OutputScriptsHash
        | Bitcoin::InputOutpointsHash
        | Bitcoin::InputAnnexesHash
        | Bitcoin::InputSequencesHash
        | Bitcoin::InputScriptSigsHash
        | Bitcoin::InputScriptsHash
        | Bitcoin::TapleafHash
        | Bitcoin::TappathHash
        | Bitcoin::InputValuesHash
        | Bitcoin::OutputValuesHash
        | Bitcoin::BuildTapleafSimplicity
        | Bitcoin::BuildTapbranch
        | Bitcoin::BuildTaptweak => TargetJetClassification::Custom(U256.into()),
        Bitcoin::OutpointHash | Bitcoin::AnnexHash => TargetJetClassification::Custom(Ctx8.into()),
        /*
         * Time locks
         */
        Bitcoin::CheckLockTime
        | Bitcoin::CheckLockHeight
        | Bitcoin::CheckLockDistance
        | Bitcoin::CheckLockDuration => TargetJetClassification::Custom(AliasedType::unit()),
        Bitcoin::TxIsFinal => TargetJetClassification::Custom(bool()),
        Bitcoin::TxLockTime => TargetJetClassification::Custom(Time.into()),
        Bitcoin::TxLockDistance => TargetJetClassification::Custom(Distance.into()),
        Bitcoin::TxLockDuration => TargetJetClassification::Custom(Duration.into()),
        Bitcoin::TxLockHeight => TargetJetClassification::Custom(Height.into()),
        /*
         * Transaction
         */
        Bitcoin::TapleafVersion => TargetJetClassification::Custom(U8.into()),
        Bitcoin::CurrentIndex
        | Bitcoin::NumInputs
        | Bitcoin::NumOutputs
        | Bitcoin::CurrentSequence
        | Bitcoin::Version
        | Bitcoin::LockTime => TargetJetClassification::Custom(U32.into()),
        Bitcoin::ScriptCMR
        | Bitcoin::CurrentScriptHash
        | Bitcoin::CurrentScriptSigHash
        | Bitcoin::TransactionId => TargetJetClassification::Custom(U256.into()),
        Bitcoin::InternalKey => TargetJetClassification::Custom(Pubkey.into()),
        Bitcoin::InputSequence => TargetJetClassification::Custom(option(U32)),
        Bitcoin::CurrentAnnexHash
        | Bitcoin::OutputScriptHash
        | Bitcoin::OutputHash
        | Bitcoin::InputScriptHash
        | Bitcoin::InputScriptSigHash
        | Bitcoin::InputHash
        | Bitcoin::InputUtxoHash
        | Bitcoin::Tappath => TargetJetClassification::Custom(option(U256)),
        Bitcoin::InputAnnexHash => TargetJetClassification::Custom(option(option(U256))),
        Bitcoin::CurrentPrevOutpoint => TargetJetClassification::Custom(Outpoint.into()),
        Bitcoin::InputPrevOutpoint => TargetJetClassification::Custom(option(Outpoint)),
        Bitcoin::CurrentValue
        | Bitcoin::Fee
        | Bitcoin::TotalInputValue
        | Bitcoin::TotalOutputValue => TargetJetClassification::Custom(U64.into()),
        Bitcoin::InputValue => TargetJetClassification::Custom(option(U64)),
        Bitcoin::OutputValue => TargetJetClassification::Custom(option(U64)),
    }
}
