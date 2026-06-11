use crate::jet::JetHL;
use crate::types::BuiltinAlias::*;
use crate::types::UIntType::*;

use super::*;

use simplicity::jet::{Core, Jet};

impl JetHL for Core {
    fn source_jet_classification(&self) -> SourceJetClassification {
        source_jet_classification(*self)
    }

    fn target_jet_classification(&self) -> TargetJetClassification {
        target_jet_classification(*self)
    }

    fn is_disabled(&self) -> bool {
        matches!(self, Core::CheckSigVerify | Core::Verify)
    }

    fn clone_box(&self) -> Box<dyn JetHL> {
        Box::new(*self)
    }

    fn as_jet(&self) -> &dyn Jet {
        self
    }
}

fn source_jet_classification(jet: Core) -> SourceJetClassification {
    match jet {
        /*
         * ==============================
         *          Core jets
         * ==============================
         *
         * Multi-bit logic
         */
        Core::Low1
        | Core::Low8
        | Core::Low16
        | Core::Low32
        | Core::Low64
        | Core::High1
        | Core::High8
        | Core::High16
        | Core::High32
        | Core::High64 => SourceJetClassification::Unary,
        Core::Verify => SourceJetClassification::Custom(vec![bool()]),
        Core::Complement1
        | Core::Some1
        | Core::LeftPadLow1_8
        | Core::LeftPadLow1_16
        | Core::LeftPadLow1_32
        | Core::LeftPadLow1_64
        | Core::LeftPadHigh1_8
        | Core::LeftPadHigh1_16
        | Core::LeftPadHigh1_32
        | Core::LeftPadHigh1_64
        | Core::LeftExtend1_8
        | Core::LeftExtend1_16
        | Core::LeftExtend1_32
        | Core::LeftExtend1_64
        | Core::RightPadLow1_8
        | Core::RightPadLow1_16
        | Core::RightPadLow1_32
        | Core::RightPadLow1_64
        | Core::RightPadHigh1_8
        | Core::RightPadHigh1_16
        | Core::RightPadHigh1_32
        | Core::RightPadHigh1_64 => SourceJetClassification::Unary,
        Core::Complement8
        | Core::Some8
        | Core::All8
        | Core::Leftmost8_1
        | Core::Leftmost8_2
        | Core::Leftmost8_4
        | Core::Rightmost8_1
        | Core::Rightmost8_2
        | Core::Rightmost8_4
        | Core::LeftPadLow8_16
        | Core::LeftPadLow8_32
        | Core::LeftPadLow8_64
        | Core::LeftPadHigh8_16
        | Core::LeftPadHigh8_32
        | Core::LeftPadHigh8_64
        | Core::LeftExtend8_16
        | Core::LeftExtend8_32
        | Core::LeftExtend8_64
        | Core::RightPadLow8_16
        | Core::RightPadLow8_32
        | Core::RightPadLow8_64
        | Core::RightPadHigh8_16
        | Core::RightPadHigh8_32
        | Core::RightPadHigh8_64
        | Core::RightExtend8_16
        | Core::RightExtend8_32
        | Core::RightExtend8_64 => SourceJetClassification::Unary,
        Core::Complement16
        | Core::Some16
        | Core::All16
        | Core::Leftmost16_1
        | Core::Leftmost16_2
        | Core::Leftmost16_4
        | Core::Leftmost16_8
        | Core::Rightmost16_1
        | Core::Rightmost16_2
        | Core::Rightmost16_4
        | Core::Rightmost16_8
        | Core::LeftPadLow16_32
        | Core::LeftPadLow16_64
        | Core::LeftPadHigh16_32
        | Core::LeftPadHigh16_64
        | Core::LeftExtend16_32
        | Core::LeftExtend16_64
        | Core::RightPadLow16_32
        | Core::RightPadLow16_64
        | Core::RightPadHigh16_32
        | Core::RightPadHigh16_64
        | Core::RightExtend16_32
        | Core::RightExtend16_64 => SourceJetClassification::Unary,
        Core::Complement32
        | Core::Some32
        | Core::All32
        | Core::Leftmost32_1
        | Core::Leftmost32_2
        | Core::Leftmost32_4
        | Core::Leftmost32_8
        | Core::Leftmost32_16
        | Core::Rightmost32_1
        | Core::Rightmost32_2
        | Core::Rightmost32_4
        | Core::Rightmost32_8
        | Core::Rightmost32_16
        | Core::LeftPadLow32_64
        | Core::LeftPadHigh32_64
        | Core::LeftExtend32_64
        | Core::RightPadLow32_64
        | Core::RightPadHigh32_64
        | Core::RightExtend32_64 => SourceJetClassification::Unary,
        Core::Complement64
        | Core::Some64
        | Core::All64
        | Core::Leftmost64_1
        | Core::Leftmost64_2
        | Core::Leftmost64_4
        | Core::Leftmost64_8
        | Core::Leftmost64_16
        | Core::Leftmost64_32
        | Core::Rightmost64_1
        | Core::Rightmost64_2
        | Core::Rightmost64_4
        | Core::Rightmost64_8
        | Core::Rightmost64_16
        | Core::Rightmost64_32 => SourceJetClassification::Unary,
        Core::And1 | Core::Or1 | Core::Xor1 | Core::Eq1 => SourceJetClassification::Binary,
        Core::And8 | Core::Or8 | Core::Xor8 | Core::Eq8 => SourceJetClassification::Binary,
        Core::And16 | Core::Or16 | Core::Xor16 | Core::Eq16 => SourceJetClassification::Binary,
        Core::And32 | Core::Or32 | Core::Xor32 | Core::Eq32 => SourceJetClassification::Binary,
        Core::And64 | Core::Or64 | Core::Xor64 | Core::Eq64 => SourceJetClassification::Binary,
        Core::Eq256 => SourceJetClassification::Binary,
        Core::Maj1 | Core::XorXor1 | Core::Ch1 => SourceJetClassification::Ternary,
        Core::Maj8 | Core::XorXor8 | Core::Ch8 => SourceJetClassification::Ternary,
        Core::Maj16 | Core::XorXor16 | Core::Ch16 => {
            SourceJetClassification::Custom(vec![U16.into(), tuple([U16, U16])])
        }
        Core::Maj32 | Core::XorXor32 | Core::Ch32 => {
            SourceJetClassification::Custom(vec![U32.into(), tuple([U32, U32])])
        }
        Core::Maj64 | Core::XorXor64 | Core::Ch64 => {
            SourceJetClassification::Custom(vec![U64.into(), tuple([U64, U64])])
        }
        Core::FullLeftShift8_1 => SourceJetClassification::Custom(vec![U8.into(), U1.into()]),
        Core::FullLeftShift8_2 => SourceJetClassification::Custom(vec![U8.into(), U2.into()]),
        Core::FullLeftShift8_4 => SourceJetClassification::Custom(vec![U8.into(), U4.into()]),
        Core::FullLeftShift16_1 => SourceJetClassification::Custom(vec![U16.into(), U1.into()]),
        Core::FullLeftShift16_2 => SourceJetClassification::Custom(vec![U16.into(), U2.into()]),
        Core::FullLeftShift16_4 => SourceJetClassification::Custom(vec![U16.into(), U4.into()]),
        Core::FullLeftShift16_8 => SourceJetClassification::Custom(vec![U16.into(), U8.into()]),
        Core::FullLeftShift32_1 => SourceJetClassification::Custom(vec![U32.into(), U1.into()]),
        Core::FullLeftShift32_2 => SourceJetClassification::Custom(vec![U32.into(), U2.into()]),
        Core::FullLeftShift32_4 => SourceJetClassification::Custom(vec![U32.into(), U4.into()]),
        Core::FullLeftShift32_8 => SourceJetClassification::Custom(vec![U32.into(), U8.into()]),
        Core::FullLeftShift32_16 => SourceJetClassification::Custom(vec![U32.into(), U16.into()]),
        Core::FullLeftShift64_1 => SourceJetClassification::Custom(vec![U64.into(), U1.into()]),
        Core::FullLeftShift64_2 => SourceJetClassification::Custom(vec![U64.into(), U2.into()]),
        Core::FullLeftShift64_4 => SourceJetClassification::Custom(vec![U64.into(), U4.into()]),
        Core::FullLeftShift64_8 => SourceJetClassification::Custom(vec![U64.into(), U8.into()]),
        Core::FullLeftShift64_16 => SourceJetClassification::Custom(vec![U64.into(), U16.into()]),
        Core::FullLeftShift64_32 => SourceJetClassification::Custom(vec![U64.into(), U32.into()]),
        Core::FullRightShift8_1 => SourceJetClassification::Custom(vec![U1.into(), U8.into()]),
        Core::FullRightShift8_2 => SourceJetClassification::Custom(vec![U2.into(), U8.into()]),
        Core::FullRightShift8_4 => SourceJetClassification::Custom(vec![U4.into(), U8.into()]),
        Core::FullRightShift16_1 => SourceJetClassification::Custom(vec![U1.into(), U16.into()]),
        Core::FullRightShift16_2 => SourceJetClassification::Custom(vec![U2.into(), U16.into()]),
        Core::FullRightShift16_4 => SourceJetClassification::Custom(vec![U4.into(), U16.into()]),
        Core::FullRightShift16_8 => SourceJetClassification::Custom(vec![U8.into(), U16.into()]),
        Core::FullRightShift32_1 => SourceJetClassification::Custom(vec![U1.into(), U32.into()]),
        Core::FullRightShift32_2 => SourceJetClassification::Custom(vec![U2.into(), U32.into()]),
        Core::FullRightShift32_4 => SourceJetClassification::Custom(vec![U4.into(), U32.into()]),
        Core::FullRightShift32_8 => SourceJetClassification::Custom(vec![U8.into(), U32.into()]),
        Core::FullRightShift32_16 => SourceJetClassification::Custom(vec![U16.into(), U32.into()]),
        Core::FullRightShift64_1 => SourceJetClassification::Custom(vec![U1.into(), U64.into()]),
        Core::FullRightShift64_2 => SourceJetClassification::Custom(vec![U2.into(), U64.into()]),
        Core::FullRightShift64_4 => SourceJetClassification::Custom(vec![U4.into(), U64.into()]),
        Core::FullRightShift64_8 => SourceJetClassification::Custom(vec![U8.into(), U64.into()]),
        Core::FullRightShift64_16 => SourceJetClassification::Custom(vec![U16.into(), U64.into()]),
        Core::FullRightShift64_32 => SourceJetClassification::Custom(vec![U32.into(), U64.into()]),
        Core::LeftShiftWith8 | Core::RightShiftWith8 => {
            SourceJetClassification::Custom(vec![U1.into(), U4.into(), U8.into()])
        }
        Core::LeftShiftWith16 | Core::RightShiftWith16 => {
            SourceJetClassification::Custom(vec![U1.into(), U4.into(), U16.into()])
        }
        Core::LeftShiftWith32 | Core::RightShiftWith32 => {
            SourceJetClassification::Custom(vec![U1.into(), U8.into(), U32.into()])
        }
        Core::LeftShiftWith64 | Core::RightShiftWith64 => {
            SourceJetClassification::Custom(vec![U1.into(), U8.into(), U64.into()])
        }
        Core::LeftShift8 | Core::RightShift8 | Core::LeftRotate8 | Core::RightRotate8 => {
            SourceJetClassification::Custom(vec![U4.into(), U8.into()])
        }
        Core::LeftShift16 | Core::RightShift16 | Core::LeftRotate16 | Core::RightRotate16 => {
            SourceJetClassification::Custom(vec![U4.into(), U16.into()])
        }
        Core::LeftShift32 | Core::RightShift32 | Core::LeftRotate32 | Core::RightRotate32 => {
            SourceJetClassification::Custom(vec![U8.into(), U32.into()])
        }
        Core::LeftShift64 | Core::RightShift64 | Core::LeftRotate64 | Core::RightRotate64 => {
            SourceJetClassification::Custom(vec![U8.into(), U64.into()])
        }
        /*
         * Arithmetic
         */
        Core::One8 | Core::One16 | Core::One32 | Core::One64 => SourceJetClassification::Unary,
        Core::Increment8 | Core::Negate8 | Core::Decrement8 | Core::IsZero8 | Core::IsOne8 => {
            SourceJetClassification::Unary
        }
        Core::Increment16 | Core::Negate16 | Core::Decrement16 | Core::IsZero16 | Core::IsOne16 => {
            SourceJetClassification::Unary
        }
        Core::Increment32 | Core::Negate32 | Core::Decrement32 | Core::IsZero32 | Core::IsOne32 => {
            SourceJetClassification::Unary
        }
        Core::Increment64 | Core::Negate64 | Core::Decrement64 | Core::IsZero64 | Core::IsOne64 => {
            SourceJetClassification::Unary
        }
        Core::Add8
        | Core::Subtract8
        | Core::Multiply8
        | Core::Le8
        | Core::Lt8
        | Core::Min8
        | Core::Max8
        | Core::DivMod8
        | Core::Divide8
        | Core::Modulo8
        | Core::Divides8 => SourceJetClassification::Binary,
        Core::Add16
        | Core::Subtract16
        | Core::Multiply16
        | Core::Le16
        | Core::Lt16
        | Core::Min16
        | Core::Max16
        | Core::DivMod16
        | Core::Divide16
        | Core::Modulo16
        | Core::Divides16 => SourceJetClassification::Binary,
        Core::Add32
        | Core::Subtract32
        | Core::Multiply32
        | Core::Le32
        | Core::Lt32
        | Core::Min32
        | Core::Max32
        | Core::DivMod32
        | Core::Divide32
        | Core::Modulo32
        | Core::Divides32 => SourceJetClassification::Binary,
        Core::Add64
        | Core::Subtract64
        | Core::Multiply64
        | Core::Le64
        | Core::Lt64
        | Core::Min64
        | Core::Max64
        | Core::DivMod64
        | Core::Divide64
        | Core::Modulo64
        | Core::Divides64 => SourceJetClassification::Binary,
        Core::DivMod128_64 => SourceJetClassification::Custom(vec![U128.into(), U64.into()]),
        Core::FullAdd8 | Core::FullSubtract8 => {
            SourceJetClassification::Custom(vec![bool(), U8.into(), U8.into()])
        }
        Core::FullAdd16 | Core::FullSubtract16 => {
            SourceJetClassification::Custom(vec![bool(), U16.into(), U16.into()])
        }
        Core::FullAdd32 | Core::FullSubtract32 => {
            SourceJetClassification::Custom(vec![bool(), U32.into(), U32.into()])
        }
        Core::FullAdd64 | Core::FullSubtract64 => {
            SourceJetClassification::Custom(vec![bool(), U64.into(), U64.into()])
        }
        Core::FullIncrement8 | Core::FullDecrement8 => {
            SourceJetClassification::Custom(vec![bool(), U8.into()])
        }
        Core::FullIncrement16 | Core::FullDecrement16 => {
            SourceJetClassification::Custom(vec![bool(), U16.into()])
        }
        Core::FullIncrement32 | Core::FullDecrement32 => {
            SourceJetClassification::Custom(vec![bool(), U32.into()])
        }
        Core::FullIncrement64 | Core::FullDecrement64 => {
            SourceJetClassification::Custom(vec![bool(), U64.into()])
        }
        Core::FullMultiply8 => SourceJetClassification::Quaternary,
        Core::FullMultiply16 => SourceJetClassification::Quaternary,
        Core::FullMultiply32 => SourceJetClassification::Quaternary,
        Core::FullMultiply64 => SourceJetClassification::Quaternary,
        Core::Median8 => SourceJetClassification::Ternary,
        Core::Median16 => SourceJetClassification::Ternary,
        Core::Median32 => SourceJetClassification::Ternary,
        Core::Median64 => SourceJetClassification::Ternary,
        /*
         * Hash functions
         */
        Core::Sha256Iv | Core::Sha256Ctx8Init => SourceJetClassification::Unary,
        Core::Sha256Block => SourceJetClassification::Ternary,
        Core::Sha256Ctx8Add1 => SourceJetClassification::Custom(vec![Ctx8.into(), U8.into()]),
        Core::Sha256Ctx8Add2 => SourceJetClassification::Custom(vec![Ctx8.into(), U16.into()]),
        Core::Sha256Ctx8Add4 => SourceJetClassification::Custom(vec![Ctx8.into(), U32.into()]),
        Core::Sha256Ctx8Add8 => SourceJetClassification::Custom(vec![Ctx8.into(), U64.into()]),
        Core::Sha256Ctx8Add16 => SourceJetClassification::Custom(vec![Ctx8.into(), U128.into()]),
        Core::Sha256Ctx8Add32 => SourceJetClassification::Custom(vec![Ctx8.into(), U256.into()]),
        Core::Sha256Ctx8Add64 => SourceJetClassification::Custom(vec![Ctx8.into(), array(U8, 64)]),
        Core::Sha256Ctx8Add128 => {
            SourceJetClassification::Custom(vec![Ctx8.into(), array(U8, 128)])
        }
        Core::Sha256Ctx8Add256 => {
            SourceJetClassification::Custom(vec![Ctx8.into(), array(U8, 256)])
        }
        Core::Sha256Ctx8Add512 => {
            SourceJetClassification::Custom(vec![Ctx8.into(), array(U8, 512)])
        }
        Core::Sha256Ctx8AddBuffer511 => {
            SourceJetClassification::Custom(vec![Ctx8.into(), list(U8, 512)])
        }
        Core::Sha256Ctx8Finalize => SourceJetClassification::Custom(vec![Ctx8.into()]),
        /*
         * Elliptic curve functions
         */
        // XXX: Nonstandard tuple
        Core::PointVerify1 => SourceJetClassification::Custom(vec![
            tuple([tuple([Scalar, Point]), Scalar.into()]),
            Point.into(),
        ]),
        Core::Decompress => SourceJetClassification::Custom(vec![Point.into()]),
        // XXX: Nonstandard tuple
        Core::LinearVerify1 => SourceJetClassification::Custom(vec![
            tuple([tuple([Scalar, Ge]), Scalar.into()]),
            Ge.into(),
        ]),
        // XXX: Nonstandard tuple
        Core::LinearCombination1 => {
            SourceJetClassification::Custom(vec![tuple([Scalar, Gej]), Scalar.into()])
        }
        Core::Scale => SourceJetClassification::Custom(vec![Scalar.into(), Gej.into()]),
        Core::Generate => SourceJetClassification::Custom(vec![Scalar.into()]),
        Core::GejInfinity => SourceJetClassification::Unary,
        Core::GejNormalize
        | Core::GejNegate
        | Core::GejDouble
        | Core::GejIsInfinity
        | Core::GejYIsOdd
        | Core::GejIsOnCurve => SourceJetClassification::Custom(vec![Gej.into()]),
        Core::GeNegate | Core::GeIsOnCurve => SourceJetClassification::Custom(vec![Ge.into()]),
        Core::GejAdd | Core::GejEquiv => {
            SourceJetClassification::Custom(vec![Gej.into(), Gej.into()])
        }
        Core::GejGeAddEx | Core::GejGeAdd | Core::GejGeEquiv => {
            SourceJetClassification::Custom(vec![Gej.into(), Ge.into()])
        }
        Core::GejRescale => SourceJetClassification::Custom(vec![Gej.into(), Fe.into()]),
        Core::GejXEquiv => SourceJetClassification::Custom(vec![Fe.into(), Gej.into()]),
        Core::ScalarAdd | Core::ScalarMultiply => {
            SourceJetClassification::Custom(vec![Scalar.into(), Scalar.into()])
        }
        Core::ScalarNormalize
        | Core::ScalarNegate
        | Core::ScalarSquare
        | Core::ScalarInvert
        | Core::ScalarMultiplyLambda
        | Core::ScalarIsZero => SourceJetClassification::Custom(vec![Scalar.into()]),
        Core::FeNormalize
        | Core::FeNegate
        | Core::FeSquare
        | Core::FeMultiplyBeta
        | Core::FeInvert
        | Core::FeSquareRoot
        | Core::FeIsZero
        | Core::FeIsOdd
        | Core::Swu => SourceJetClassification::Custom(vec![Fe.into()]),
        Core::FeAdd | Core::FeMultiply => {
            SourceJetClassification::Custom(vec![Fe.into(), Fe.into()])
        }
        Core::HashToCurve => SourceJetClassification::Unary,
        /*
         * Digital signatures
         */
        // XXX: Nonstandard tuple
        Core::CheckSigVerify => {
            SourceJetClassification::Custom(vec![tuple([Pubkey, Message64]), Signature.into()])
        }
        // XXX: Nonstandard tuple
        Core::Bip0340Verify => {
            SourceJetClassification::Custom(vec![tuple([Pubkey, Message]), Signature.into()])
        }
        /*
         * Bitcoin (without primitives)
         */
        Core::TapdataInit => SourceJetClassification::Unary,
        Core::ParseLock | Core::ParseSequence => SourceJetClassification::Unary,
    }
}

fn target_jet_classification(jet: Core) -> TargetJetClassification {
    match jet {
        /*
         * ==============================
         *          Core jets
         * ==============================
         *
         * Multi-bit logic
         */
        Core::Verify => TargetJetClassification::Unary,
        Core::Some1
        | Core::Some8
        | Core::Some16
        | Core::Some32
        | Core::Some64
        | Core::All8
        | Core::All16
        | Core::All32
        | Core::All64
        | Core::Eq1
        | Core::Eq8
        | Core::Eq16
        | Core::Eq32
        | Core::Eq64
        | Core::Eq256 => TargetJetClassification::Custom(bool()),
        Core::Low1
        | Core::High1
        | Core::Complement1
        | Core::And1
        | Core::Or1
        | Core::Xor1
        | Core::Maj1
        | Core::XorXor1
        | Core::Ch1
        | Core::Leftmost8_1
        | Core::Rightmost8_1
        | Core::Leftmost16_1
        | Core::Rightmost16_1
        | Core::Leftmost32_1
        | Core::Rightmost32_1
        | Core::Leftmost64_1
        | Core::Rightmost64_1 => TargetJetClassification::Unary,
        Core::Leftmost8_2
        | Core::Rightmost8_2
        | Core::Leftmost16_2
        | Core::Rightmost16_2
        | Core::Leftmost32_2
        | Core::Rightmost32_2
        | Core::Leftmost64_2
        | Core::Rightmost64_2 => TargetJetClassification::Unary,
        Core::Leftmost8_4
        | Core::Rightmost8_4
        | Core::Leftmost16_4
        | Core::Rightmost16_4
        | Core::Leftmost32_4
        | Core::Rightmost32_4
        | Core::Leftmost64_4
        | Core::Rightmost64_4 => TargetJetClassification::Unary,
        Core::Low8
        | Core::High8
        | Core::Complement8
        | Core::And8
        | Core::Or8
        | Core::Xor8
        | Core::Maj8
        | Core::XorXor8
        | Core::Ch8
        | Core::Leftmost16_8
        | Core::Rightmost16_8
        | Core::Leftmost32_8
        | Core::Rightmost32_8
        | Core::Leftmost64_8
        | Core::Rightmost64_8
        | Core::LeftPadLow1_8
        | Core::LeftPadHigh1_8
        | Core::LeftExtend1_8
        | Core::RightPadLow1_8
        | Core::RightPadHigh1_8
        | Core::LeftShiftWith8
        | Core::RightShiftWith8
        | Core::LeftShift8
        | Core::RightShift8
        | Core::LeftRotate8
        | Core::RightRotate8 => TargetJetClassification::Unary,
        Core::Low16
        | Core::High16
        | Core::Complement16
        | Core::And16
        | Core::Or16
        | Core::Xor16
        | Core::Maj16
        | Core::XorXor16
        | Core::Ch16
        | Core::Leftmost32_16
        | Core::Rightmost32_16
        | Core::Leftmost64_16
        | Core::Rightmost64_16
        | Core::LeftPadLow1_16
        | Core::LeftPadHigh1_16
        | Core::LeftExtend1_16
        | Core::RightPadLow1_16
        | Core::RightPadHigh1_16
        | Core::LeftPadLow8_16
        | Core::LeftPadHigh8_16
        | Core::LeftExtend8_16
        | Core::RightPadLow8_16
        | Core::RightPadHigh8_16
        | Core::RightExtend8_16
        | Core::LeftShiftWith16
        | Core::RightShiftWith16
        | Core::LeftShift16
        | Core::RightShift16
        | Core::LeftRotate16
        | Core::RightRotate16 => TargetJetClassification::Unary,
        Core::Low32
        | Core::High32
        | Core::Complement32
        | Core::And32
        | Core::Or32
        | Core::Xor32
        | Core::Maj32
        | Core::XorXor32
        | Core::Ch32
        | Core::Leftmost64_32
        | Core::Rightmost64_32
        | Core::LeftPadLow1_32
        | Core::LeftPadHigh1_32
        | Core::LeftExtend1_32
        | Core::RightPadLow1_32
        | Core::RightPadHigh1_32
        | Core::LeftPadLow8_32
        | Core::LeftPadHigh8_32
        | Core::LeftExtend8_32
        | Core::RightPadLow8_32
        | Core::RightPadHigh8_32
        | Core::RightExtend8_32
        | Core::LeftPadLow16_32
        | Core::LeftPadHigh16_32
        | Core::LeftExtend16_32
        | Core::RightPadLow16_32
        | Core::RightPadHigh16_32
        | Core::RightExtend16_32
        | Core::LeftShiftWith32
        | Core::RightShiftWith32
        | Core::LeftShift32
        | Core::RightShift32
        | Core::LeftRotate32
        | Core::RightRotate32 => TargetJetClassification::Unary,
        Core::Low64
        | Core::High64
        | Core::Complement64
        | Core::And64
        | Core::Or64
        | Core::Xor64
        | Core::Maj64
        | Core::XorXor64
        | Core::Ch64
        | Core::LeftPadLow1_64
        | Core::LeftPadHigh1_64
        | Core::LeftExtend1_64
        | Core::RightPadLow1_64
        | Core::RightPadHigh1_64
        | Core::LeftPadLow8_64
        | Core::LeftPadHigh8_64
        | Core::LeftExtend8_64
        | Core::RightPadLow8_64
        | Core::RightPadHigh8_64
        | Core::RightExtend8_64
        | Core::LeftPadLow16_64
        | Core::LeftPadHigh16_64
        | Core::LeftExtend16_64
        | Core::RightPadLow16_64
        | Core::RightPadHigh16_64
        | Core::RightExtend16_64
        | Core::LeftPadLow32_64
        | Core::LeftPadHigh32_64
        | Core::LeftExtend32_64
        | Core::RightPadLow32_64
        | Core::RightPadHigh32_64
        | Core::RightExtend32_64
        | Core::LeftShiftWith64
        | Core::RightShiftWith64
        | Core::LeftShift64
        | Core::RightShift64
        | Core::LeftRotate64
        | Core::RightRotate64 => TargetJetClassification::Unary,
        Core::FullLeftShift8_1 => TargetJetClassification::Custom(tuple([U1, U8])),
        Core::FullLeftShift8_2 => TargetJetClassification::Custom(tuple([U2, U8])),
        Core::FullLeftShift8_4 => TargetJetClassification::Custom(tuple([U4, U8])),
        Core::FullLeftShift16_1 => TargetJetClassification::Custom(tuple([U1, U16])),
        Core::FullLeftShift16_2 => TargetJetClassification::Custom(tuple([U2, U16])),
        Core::FullLeftShift16_4 => TargetJetClassification::Custom(tuple([U4, U16])),
        Core::FullLeftShift16_8 => TargetJetClassification::Custom(tuple([U8, U16])),
        Core::FullLeftShift32_1 => TargetJetClassification::Custom(tuple([U1, U32])),
        Core::FullLeftShift32_2 => TargetJetClassification::Custom(tuple([U2, U32])),
        Core::FullLeftShift32_4 => TargetJetClassification::Custom(tuple([U4, U32])),
        Core::FullLeftShift32_8 => TargetJetClassification::Custom(tuple([U8, U32])),
        Core::FullLeftShift32_16 => TargetJetClassification::Custom(tuple([U16, U32])),
        Core::FullLeftShift64_1 => TargetJetClassification::Custom(tuple([U1, U64])),
        Core::FullLeftShift64_2 => TargetJetClassification::Custom(tuple([U2, U64])),
        Core::FullLeftShift64_4 => TargetJetClassification::Custom(tuple([U4, U64])),
        Core::FullLeftShift64_8 => TargetJetClassification::Custom(tuple([U8, U64])),
        Core::FullLeftShift64_16 => TargetJetClassification::Custom(tuple([U16, U64])),
        Core::FullLeftShift64_32 => TargetJetClassification::Custom(tuple([U32, U64])),
        Core::FullRightShift8_1 => TargetJetClassification::Custom(tuple([U8, U1])),
        Core::FullRightShift8_2 => TargetJetClassification::Custom(tuple([U8, U2])),
        Core::FullRightShift8_4 => TargetJetClassification::Custom(tuple([U8, U4])),
        Core::FullRightShift16_1 => TargetJetClassification::Custom(tuple([U16, U1])),
        Core::FullRightShift16_2 => TargetJetClassification::Custom(tuple([U16, U2])),
        Core::FullRightShift16_4 => TargetJetClassification::Custom(tuple([U16, U4])),
        Core::FullRightShift16_8 => TargetJetClassification::Custom(tuple([U16, U8])),
        Core::FullRightShift32_1 => TargetJetClassification::Custom(tuple([U32, U1])),
        Core::FullRightShift32_2 => TargetJetClassification::Custom(tuple([U32, U2])),
        Core::FullRightShift32_4 => TargetJetClassification::Custom(tuple([U32, U4])),
        Core::FullRightShift32_8 => TargetJetClassification::Custom(tuple([U32, U8])),
        Core::FullRightShift32_16 => TargetJetClassification::Custom(tuple([U32, U16])),
        Core::FullRightShift64_1 => TargetJetClassification::Custom(tuple([U64, U1])),
        Core::FullRightShift64_2 => TargetJetClassification::Custom(tuple([U64, U2])),
        Core::FullRightShift64_4 => TargetJetClassification::Custom(tuple([U64, U4])),
        Core::FullRightShift64_8 => TargetJetClassification::Custom(tuple([U64, U8])),
        Core::FullRightShift64_16 => TargetJetClassification::Custom(tuple([U64, U16])),
        Core::FullRightShift64_32 => TargetJetClassification::Custom(tuple([U64, U32])),
        /*
         * Arithmetic
         */
        Core::Le8
        | Core::Lt8
        | Core::Le16
        | Core::Lt16
        | Core::Le32
        | Core::Lt32
        | Core::Le64
        | Core::Lt64
        | Core::IsZero8
        | Core::IsOne8
        | Core::IsZero16
        | Core::IsOne16
        | Core::IsZero32
        | Core::IsOne32
        | Core::IsZero64
        | Core::IsOne64
        | Core::Divides8
        | Core::Divides16
        | Core::Divides32
        | Core::Divides64 => TargetJetClassification::Custom(bool()),
        Core::One8 | Core::Min8 | Core::Max8 | Core::Divide8 | Core::Modulo8 | Core::Median8 => {
            TargetJetClassification::Unary
        }
        Core::One16
        | Core::Min16
        | Core::Max16
        | Core::Divide16
        | Core::Modulo16
        | Core::Multiply8
        | Core::FullMultiply8
        | Core::Median16 => TargetJetClassification::Unary,
        Core::One32
        | Core::Min32
        | Core::Max32
        | Core::Divide32
        | Core::Modulo32
        | Core::Multiply16
        | Core::FullMultiply16
        | Core::Median32 => TargetJetClassification::Unary,
        Core::One64
        | Core::Min64
        | Core::Max64
        | Core::Divide64
        | Core::Modulo64
        | Core::Multiply32
        | Core::FullMultiply32
        | Core::Median64 => TargetJetClassification::Unary,
        Core::Multiply64 | Core::FullMultiply64 => TargetJetClassification::Unary,
        Core::Increment8
        | Core::Negate8
        | Core::Decrement8
        | Core::Add8
        | Core::Subtract8
        | Core::FullAdd8
        | Core::FullSubtract8
        | Core::FullIncrement8
        | Core::FullDecrement8 => TargetJetClassification::Custom(tuple([bool(), U8.into()])),
        Core::Increment16
        | Core::Negate16
        | Core::Decrement16
        | Core::Add16
        | Core::Subtract16
        | Core::FullAdd16
        | Core::FullSubtract16
        | Core::FullIncrement16
        | Core::FullDecrement16 => TargetJetClassification::Custom(tuple([bool(), U16.into()])),
        Core::Increment32
        | Core::Negate32
        | Core::Decrement32
        | Core::Add32
        | Core::Subtract32
        | Core::FullAdd32
        | Core::FullSubtract32
        | Core::FullIncrement32
        | Core::FullDecrement32 => TargetJetClassification::Custom(tuple([bool(), U32.into()])),
        Core::Increment64
        | Core::Negate64
        | Core::Decrement64
        | Core::Add64
        | Core::Subtract64
        | Core::FullAdd64
        | Core::FullSubtract64
        | Core::FullIncrement64
        | Core::FullDecrement64 => TargetJetClassification::Custom(tuple([bool(), U64.into()])),
        Core::DivMod8 => TargetJetClassification::Custom(tuple([U8, U8])),
        Core::DivMod16 => TargetJetClassification::Custom(tuple([U16, U16])),
        Core::DivMod32 => TargetJetClassification::Custom(tuple([U32, U32])),
        Core::DivMod64 => TargetJetClassification::Custom(tuple([U64, U64])),
        Core::DivMod128_64 => TargetJetClassification::Custom(tuple([U64, U64])),
        /*
         * Hash functions
         */
        Core::Sha256Iv | Core::Sha256Block | Core::Sha256Ctx8Finalize => {
            TargetJetClassification::Unary
        }
        Core::Sha256Ctx8Init
        | Core::Sha256Ctx8Add1
        | Core::Sha256Ctx8Add2
        | Core::Sha256Ctx8Add4
        | Core::Sha256Ctx8Add8
        | Core::Sha256Ctx8Add16
        | Core::Sha256Ctx8Add32
        | Core::Sha256Ctx8Add64
        | Core::Sha256Ctx8Add128
        | Core::Sha256Ctx8Add256
        | Core::Sha256Ctx8Add512
        | Core::Sha256Ctx8AddBuffer511 => TargetJetClassification::Custom(Ctx8.into()),
        /*
         * Elliptic curve functions
         */
        Core::PointVerify1 | Core::LinearVerify1 => TargetJetClassification::Unary,
        Core::GejIsInfinity
        | Core::GejEquiv
        | Core::GejGeEquiv
        | Core::GejXEquiv
        | Core::GejYIsOdd
        | Core::GejIsOnCurve
        | Core::GeIsOnCurve
        | Core::ScalarIsZero
        | Core::FeIsZero
        | Core::FeIsOdd => TargetJetClassification::Custom(bool()),
        Core::GeNegate | Core::HashToCurve | Core::Swu => {
            TargetJetClassification::Custom(Ge.into())
        }
        Core::Decompress | Core::GejNormalize => TargetJetClassification::Custom(option(Ge)),
        Core::LinearCombination1
        | Core::Scale
        | Core::Generate
        | Core::GejInfinity
        | Core::GejNegate
        | Core::GejDouble
        | Core::GejAdd
        | Core::GejGeAdd
        | Core::GejRescale => TargetJetClassification::Custom(Gej.into()),
        Core::GejGeAddEx => TargetJetClassification::Custom(tuple([Fe, Gej])),
        Core::ScalarNormalize
        | Core::ScalarNegate
        | Core::ScalarAdd
        | Core::ScalarSquare
        | Core::ScalarMultiply
        | Core::ScalarMultiplyLambda
        | Core::ScalarInvert => TargetJetClassification::Custom(Scalar.into()),
        Core::FeNormalize
        | Core::FeNegate
        | Core::FeAdd
        | Core::FeSquare
        | Core::FeMultiply
        | Core::FeMultiplyBeta
        | Core::FeInvert => TargetJetClassification::Custom(Fe.into()),
        Core::FeSquareRoot => TargetJetClassification::Custom(option(Fe)),
        /*
         * Digital signatures
         */
        Core::CheckSigVerify | Core::Bip0340Verify => TargetJetClassification::Unary,
        /*
         * Bitcoin (without primitives)
         */
        Core::ParseLock => TargetJetClassification::Custom(either(Height, Time)),
        Core::ParseSequence => TargetJetClassification::Custom(option(either(Distance, Duration))),
        Core::TapdataInit => TargetJetClassification::Custom(Ctx8.into()),
    }
}
