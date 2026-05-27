use crate::jet::JetHL;
use crate::types::BuiltinAlias::*;
use crate::types::UIntType::*;
use crate::types::*;

use super::*;

use simplicity::jet::{Core, Jet};

impl JetHL for Core {
    fn source_type(&self) -> Vec<AliasedType> {
        source_type(*self)
    }

    fn target_type(&self) -> AliasedType {
        target_type(*self)
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

pub fn source_type(jet: Core) -> Vec<AliasedType> {
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
        | Core::High64 => vec![],
        Core::Verify => vec![bool()],
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
        | Core::RightPadHigh1_64 => vec![U1.into()],
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
        | Core::RightExtend8_64 => vec![U8.into()],
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
        | Core::RightExtend16_64 => vec![U16.into()],
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
        | Core::RightExtend32_64 => vec![U32.into()],
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
        | Core::Rightmost64_32 => vec![U64.into()],
        Core::And1 | Core::Or1 | Core::Xor1 | Core::Eq1 => {
            vec![U1.into(), U1.into()]
        }
        Core::And8 | Core::Or8 | Core::Xor8 | Core::Eq8 => {
            vec![U8.into(), U8.into()]
        }
        Core::And16 | Core::Or16 | Core::Xor16 | Core::Eq16 => {
            vec![U16.into(), U16.into()]
        }
        Core::And32 | Core::Or32 | Core::Xor32 | Core::Eq32 => {
            vec![U32.into(), U32.into()]
        }
        Core::And64 | Core::Or64 | Core::Xor64 | Core::Eq64 => {
            vec![U64.into(), U64.into()]
        }
        Core::Eq256 => vec![U256.into(), U256.into()],
        Core::Maj1 | Core::XorXor1 | Core::Ch1 => vec![U1.into(), U1.into(), U1.into()],
        Core::Maj8 | Core::XorXor8 | Core::Ch8 => vec![U8.into(), U8.into(), U8.into()],
        Core::Maj16 | Core::XorXor16 | Core::Ch16 => {
            vec![U16.into(), tuple([U16, U16])]
        }
        Core::Maj32 | Core::XorXor32 | Core::Ch32 => {
            vec![U32.into(), tuple([U32, U32])]
        }
        Core::Maj64 | Core::XorXor64 | Core::Ch64 => {
            vec![U64.into(), tuple([U64, U64])]
        }
        Core::FullLeftShift8_1 => vec![U8.into(), U1.into()],
        Core::FullLeftShift8_2 => vec![U8.into(), U2.into()],
        Core::FullLeftShift8_4 => vec![U8.into(), U4.into()],
        Core::FullLeftShift16_1 => vec![U16.into(), U1.into()],
        Core::FullLeftShift16_2 => vec![U16.into(), U2.into()],
        Core::FullLeftShift16_4 => vec![U16.into(), U4.into()],
        Core::FullLeftShift16_8 => vec![U16.into(), U8.into()],
        Core::FullLeftShift32_1 => vec![U32.into(), U1.into()],
        Core::FullLeftShift32_2 => vec![U32.into(), U2.into()],
        Core::FullLeftShift32_4 => vec![U32.into(), U4.into()],
        Core::FullLeftShift32_8 => vec![U32.into(), U8.into()],
        Core::FullLeftShift32_16 => vec![U32.into(), U16.into()],
        Core::FullLeftShift64_1 => vec![U64.into(), U1.into()],
        Core::FullLeftShift64_2 => vec![U64.into(), U2.into()],
        Core::FullLeftShift64_4 => vec![U64.into(), U4.into()],
        Core::FullLeftShift64_8 => vec![U64.into(), U8.into()],
        Core::FullLeftShift64_16 => vec![U64.into(), U16.into()],
        Core::FullLeftShift64_32 => vec![U64.into(), U32.into()],
        Core::FullRightShift8_1 => vec![U1.into(), U8.into()],
        Core::FullRightShift8_2 => vec![U2.into(), U8.into()],
        Core::FullRightShift8_4 => vec![U4.into(), U8.into()],
        Core::FullRightShift16_1 => vec![U1.into(), U16.into()],
        Core::FullRightShift16_2 => vec![U2.into(), U16.into()],
        Core::FullRightShift16_4 => vec![U4.into(), U16.into()],
        Core::FullRightShift16_8 => vec![U8.into(), U16.into()],
        Core::FullRightShift32_1 => vec![U1.into(), U32.into()],
        Core::FullRightShift32_2 => vec![U2.into(), U32.into()],
        Core::FullRightShift32_4 => vec![U4.into(), U32.into()],
        Core::FullRightShift32_8 => vec![U8.into(), U32.into()],
        Core::FullRightShift32_16 => vec![U16.into(), U32.into()],
        Core::FullRightShift64_1 => vec![U1.into(), U64.into()],
        Core::FullRightShift64_2 => vec![U2.into(), U64.into()],
        Core::FullRightShift64_4 => vec![U4.into(), U64.into()],
        Core::FullRightShift64_8 => vec![U8.into(), U64.into()],
        Core::FullRightShift64_16 => vec![U16.into(), U64.into()],
        Core::FullRightShift64_32 => vec![U32.into(), U64.into()],
        Core::LeftShiftWith8 | Core::RightShiftWith8 => {
            vec![U1.into(), U4.into(), U8.into()]
        }
        Core::LeftShiftWith16 | Core::RightShiftWith16 => {
            vec![U1.into(), U4.into(), U16.into()]
        }
        Core::LeftShiftWith32 | Core::RightShiftWith32 => {
            vec![U1.into(), U8.into(), U32.into()]
        }
        Core::LeftShiftWith64 | Core::RightShiftWith64 => {
            vec![U1.into(), U8.into(), U64.into()]
        }
        Core::LeftShift8 | Core::RightShift8 | Core::LeftRotate8 | Core::RightRotate8 => {
            vec![U4.into(), U8.into()]
        }
        Core::LeftShift16 | Core::RightShift16 | Core::LeftRotate16 | Core::RightRotate16 => {
            vec![U4.into(), U16.into()]
        }
        Core::LeftShift32 | Core::RightShift32 | Core::LeftRotate32 | Core::RightRotate32 => {
            vec![U8.into(), U32.into()]
        }
        Core::LeftShift64 | Core::RightShift64 | Core::LeftRotate64 | Core::RightRotate64 => {
            vec![U8.into(), U64.into()]
        }
        /*
         * Arithmetic
         */
        Core::One8 | Core::One16 | Core::One32 | Core::One64 => vec![],
        Core::Increment8 | Core::Negate8 | Core::Decrement8 | Core::IsZero8 | Core::IsOne8 => {
            vec![U8.into()]
        }
        Core::Increment16 | Core::Negate16 | Core::Decrement16 | Core::IsZero16 | Core::IsOne16 => {
            vec![U16.into()]
        }
        Core::Increment32 | Core::Negate32 | Core::Decrement32 | Core::IsZero32 | Core::IsOne32 => {
            vec![U32.into()]
        }
        Core::Increment64 | Core::Negate64 | Core::Decrement64 | Core::IsZero64 | Core::IsOne64 => {
            vec![U64.into()]
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
        | Core::Divides8 => vec![U8.into(), U8.into()],
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
        | Core::Divides16 => vec![U16.into(), U16.into()],
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
        | Core::Divides32 => vec![U32.into(), U32.into()],
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
        | Core::Divides64 => vec![U64.into(), U64.into()],
        Core::DivMod128_64 => vec![U128.into(), U64.into()],
        Core::FullAdd8 | Core::FullSubtract8 => vec![bool(), U8.into(), U8.into()],
        Core::FullAdd16 | Core::FullSubtract16 => vec![bool(), U16.into(), U16.into()],
        Core::FullAdd32 | Core::FullSubtract32 => vec![bool(), U32.into(), U32.into()],
        Core::FullAdd64 | Core::FullSubtract64 => vec![bool(), U64.into(), U64.into()],
        Core::FullIncrement8 | Core::FullDecrement8 => vec![bool(), U8.into()],
        Core::FullIncrement16 | Core::FullDecrement16 => vec![bool(), U16.into()],
        Core::FullIncrement32 | Core::FullDecrement32 => vec![bool(), U32.into()],
        Core::FullIncrement64 | Core::FullDecrement64 => vec![bool(), U64.into()],
        Core::FullMultiply8 => vec![U8.into(), U8.into(), U8.into(), U8.into()],
        Core::FullMultiply16 => vec![U16.into(), U16.into(), U16.into(), U16.into()],
        Core::FullMultiply32 => vec![U32.into(), U32.into(), U32.into(), U32.into()],
        Core::FullMultiply64 => vec![U64.into(), U64.into(), U64.into(), U64.into()],
        Core::Median8 => vec![U8.into(), U8.into(), U8.into()],
        Core::Median16 => vec![U16.into(), U16.into(), U16.into()],
        Core::Median32 => vec![U32.into(), U32.into(), U32.into()],
        Core::Median64 => vec![U64.into(), U64.into(), U64.into()],
        /*
         * Hash functions
         */
        Core::Sha256Iv | Core::Sha256Ctx8Init => vec![],
        Core::Sha256Block => vec![U256.into(), U256.into(), U256.into()],
        Core::Sha256Ctx8Add1 => vec![Ctx8.into(), U8.into()],
        Core::Sha256Ctx8Add2 => vec![Ctx8.into(), U16.into()],
        Core::Sha256Ctx8Add4 => vec![Ctx8.into(), U32.into()],
        Core::Sha256Ctx8Add8 => vec![Ctx8.into(), U64.into()],
        Core::Sha256Ctx8Add16 => vec![Ctx8.into(), U128.into()],
        Core::Sha256Ctx8Add32 => vec![Ctx8.into(), U256.into()],
        Core::Sha256Ctx8Add64 => vec![Ctx8.into(), array(U8, 64)],
        Core::Sha256Ctx8Add128 => vec![Ctx8.into(), array(U8, 128)],
        Core::Sha256Ctx8Add256 => vec![Ctx8.into(), array(U8, 256)],
        Core::Sha256Ctx8Add512 => vec![Ctx8.into(), array(U8, 512)],
        Core::Sha256Ctx8AddBuffer511 => vec![Ctx8.into(), list(U8, 512)],
        Core::Sha256Ctx8Finalize => vec![Ctx8.into()],
        /*
         * Elliptic curve functions
         */
        // XXX: Nonstandard tuple
        Core::PointVerify1 => {
            vec![tuple([tuple([Scalar, Point]), Scalar.into()]), Point.into()]
        }
        Core::Decompress => vec![Point.into()],
        // XXX: Nonstandard tuple
        Core::LinearVerify1 => vec![tuple([tuple([Scalar, Ge]), Scalar.into()]), Ge.into()],
        // XXX: Nonstandard tuple
        Core::LinearCombination1 => vec![tuple([Scalar, Gej]), Scalar.into()],
        Core::Scale => vec![Scalar.into(), Gej.into()],
        Core::Generate => vec![Scalar.into()],
        Core::GejInfinity => vec![],
        Core::GejNormalize
        | Core::GejNegate
        | Core::GejDouble
        | Core::GejIsInfinity
        | Core::GejYIsOdd
        | Core::GejIsOnCurve => vec![Gej.into()],
        Core::GeNegate | Core::GeIsOnCurve => vec![Ge.into()],
        Core::GejAdd | Core::GejEquiv => vec![Gej.into(), Gej.into()],
        Core::GejGeAddEx | Core::GejGeAdd | Core::GejGeEquiv => {
            vec![Gej.into(), Ge.into()]
        }
        Core::GejRescale => vec![Gej.into(), Fe.into()],
        Core::GejXEquiv => vec![Fe.into(), Gej.into()],
        Core::ScalarAdd | Core::ScalarMultiply => vec![Scalar.into(), Scalar.into()],
        Core::ScalarNormalize
        | Core::ScalarNegate
        | Core::ScalarSquare
        | Core::ScalarInvert
        | Core::ScalarMultiplyLambda
        | Core::ScalarIsZero => vec![Scalar.into()],
        Core::FeNormalize
        | Core::FeNegate
        | Core::FeSquare
        | Core::FeMultiplyBeta
        | Core::FeInvert
        | Core::FeSquareRoot
        | Core::FeIsZero
        | Core::FeIsOdd
        | Core::Swu => vec![Fe.into()],
        Core::FeAdd | Core::FeMultiply => vec![Fe.into(), Fe.into()],
        Core::HashToCurve => vec![U256.into()],
        /*
         * Digital signatures
         */
        // XXX: Nonstandard tuple
        Core::CheckSigVerify => vec![tuple([Pubkey, Message64]), Signature.into()],
        // XXX: Nonstandard tuple
        Core::Bip0340Verify => vec![tuple([Pubkey, Message]), Signature.into()],
        /*
         * Bitcoin (without primitives)
         */
        Core::TapdataInit => vec![],
        Core::ParseLock | Core::ParseSequence => vec![U32.into()],
    }
}

pub fn target_type(jet: Core) -> AliasedType {
    match jet {
        /*
         * ==============================
         *          Core jets
         * ==============================
         *
         * Multi-bit logic
         */
        Core::Verify => AliasedType::unit(),
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
        | Core::Eq256 => bool(),
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
        | Core::Rightmost64_1 => U1.into(),
        Core::Leftmost8_2
        | Core::Rightmost8_2
        | Core::Leftmost16_2
        | Core::Rightmost16_2
        | Core::Leftmost32_2
        | Core::Rightmost32_2
        | Core::Leftmost64_2
        | Core::Rightmost64_2 => U2.into(),
        Core::Leftmost8_4
        | Core::Rightmost8_4
        | Core::Leftmost16_4
        | Core::Rightmost16_4
        | Core::Leftmost32_4
        | Core::Rightmost32_4
        | Core::Leftmost64_4
        | Core::Rightmost64_4 => U4.into(),
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
        | Core::RightRotate8 => U8.into(),
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
        | Core::RightRotate16 => U16.into(),
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
        | Core::RightRotate32 => U32.into(),
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
        | Core::RightRotate64 => U64.into(),
        Core::FullLeftShift8_1 => tuple([U1, U8]),
        Core::FullLeftShift8_2 => tuple([U2, U8]),
        Core::FullLeftShift8_4 => tuple([U4, U8]),
        Core::FullLeftShift16_1 => tuple([U1, U16]),
        Core::FullLeftShift16_2 => tuple([U2, U16]),
        Core::FullLeftShift16_4 => tuple([U4, U16]),
        Core::FullLeftShift16_8 => tuple([U8, U16]),
        Core::FullLeftShift32_1 => tuple([U1, U32]),
        Core::FullLeftShift32_2 => tuple([U2, U32]),
        Core::FullLeftShift32_4 => tuple([U4, U32]),
        Core::FullLeftShift32_8 => tuple([U8, U32]),
        Core::FullLeftShift32_16 => tuple([U16, U32]),
        Core::FullLeftShift64_1 => tuple([U1, U64]),
        Core::FullLeftShift64_2 => tuple([U2, U64]),
        Core::FullLeftShift64_4 => tuple([U4, U64]),
        Core::FullLeftShift64_8 => tuple([U8, U64]),
        Core::FullLeftShift64_16 => tuple([U16, U64]),
        Core::FullLeftShift64_32 => tuple([U32, U64]),
        Core::FullRightShift8_1 => tuple([U8, U1]),
        Core::FullRightShift8_2 => tuple([U8, U2]),
        Core::FullRightShift8_4 => tuple([U8, U4]),
        Core::FullRightShift16_1 => tuple([U16, U1]),
        Core::FullRightShift16_2 => tuple([U16, U2]),
        Core::FullRightShift16_4 => tuple([U16, U4]),
        Core::FullRightShift16_8 => tuple([U16, U8]),
        Core::FullRightShift32_1 => tuple([U32, U1]),
        Core::FullRightShift32_2 => tuple([U32, U2]),
        Core::FullRightShift32_4 => tuple([U32, U4]),
        Core::FullRightShift32_8 => tuple([U32, U8]),
        Core::FullRightShift32_16 => tuple([U32, U16]),
        Core::FullRightShift64_1 => tuple([U64, U1]),
        Core::FullRightShift64_2 => tuple([U64, U2]),
        Core::FullRightShift64_4 => tuple([U64, U4]),
        Core::FullRightShift64_8 => tuple([U64, U8]),
        Core::FullRightShift64_16 => tuple([U64, U16]),
        Core::FullRightShift64_32 => tuple([U64, U32]),
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
        | Core::Divides64 => bool(),
        Core::One8 | Core::Min8 | Core::Max8 | Core::Divide8 | Core::Modulo8 | Core::Median8 => {
            U8.into()
        }
        Core::One16
        | Core::Min16
        | Core::Max16
        | Core::Divide16
        | Core::Modulo16
        | Core::Multiply8
        | Core::FullMultiply8
        | Core::Median16 => U16.into(),
        Core::One32
        | Core::Min32
        | Core::Max32
        | Core::Divide32
        | Core::Modulo32
        | Core::Multiply16
        | Core::FullMultiply16
        | Core::Median32 => U32.into(),
        Core::One64
        | Core::Min64
        | Core::Max64
        | Core::Divide64
        | Core::Modulo64
        | Core::Multiply32
        | Core::FullMultiply32
        | Core::Median64 => U64.into(),
        Core::Multiply64 | Core::FullMultiply64 => U128.into(),
        Core::Increment8
        | Core::Negate8
        | Core::Decrement8
        | Core::Add8
        | Core::Subtract8
        | Core::FullAdd8
        | Core::FullSubtract8
        | Core::FullIncrement8
        | Core::FullDecrement8 => tuple([bool(), U8.into()]),
        Core::Increment16
        | Core::Negate16
        | Core::Decrement16
        | Core::Add16
        | Core::Subtract16
        | Core::FullAdd16
        | Core::FullSubtract16
        | Core::FullIncrement16
        | Core::FullDecrement16 => tuple([bool(), U16.into()]),
        Core::Increment32
        | Core::Negate32
        | Core::Decrement32
        | Core::Add32
        | Core::Subtract32
        | Core::FullAdd32
        | Core::FullSubtract32
        | Core::FullIncrement32
        | Core::FullDecrement32 => tuple([bool(), U32.into()]),
        Core::Increment64
        | Core::Negate64
        | Core::Decrement64
        | Core::Add64
        | Core::Subtract64
        | Core::FullAdd64
        | Core::FullSubtract64
        | Core::FullIncrement64
        | Core::FullDecrement64 => tuple([bool(), U64.into()]),
        Core::DivMod8 => tuple([U8, U8]),
        Core::DivMod16 => tuple([U16, U16]),
        Core::DivMod32 => tuple([U32, U32]),
        Core::DivMod64 => tuple([U64, U64]),
        Core::DivMod128_64 => tuple([U64, U64]),
        /*
         * Hash functions
         */
        Core::Sha256Iv | Core::Sha256Block | Core::Sha256Ctx8Finalize => U256.into(),
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
        | Core::Sha256Ctx8AddBuffer511 => Ctx8.into(),
        /*
         * Elliptic curve functions
         */
        Core::PointVerify1 | Core::LinearVerify1 => AliasedType::unit(),
        Core::GejIsInfinity
        | Core::GejEquiv
        | Core::GejGeEquiv
        | Core::GejXEquiv
        | Core::GejYIsOdd
        | Core::GejIsOnCurve
        | Core::GeIsOnCurve
        | Core::ScalarIsZero
        | Core::FeIsZero
        | Core::FeIsOdd => bool(),
        Core::GeNegate | Core::HashToCurve | Core::Swu => Ge.into(),
        Core::Decompress | Core::GejNormalize => option(Ge),
        Core::LinearCombination1
        | Core::Scale
        | Core::Generate
        | Core::GejInfinity
        | Core::GejNegate
        | Core::GejDouble
        | Core::GejAdd
        | Core::GejGeAdd
        | Core::GejRescale => Gej.into(),
        Core::GejGeAddEx => tuple([Fe, Gej]),
        Core::ScalarNormalize
        | Core::ScalarNegate
        | Core::ScalarAdd
        | Core::ScalarSquare
        | Core::ScalarMultiply
        | Core::ScalarMultiplyLambda
        | Core::ScalarInvert => Scalar.into(),
        Core::FeNormalize
        | Core::FeNegate
        | Core::FeAdd
        | Core::FeSquare
        | Core::FeMultiply
        | Core::FeMultiplyBeta
        | Core::FeInvert => Fe.into(),
        Core::FeSquareRoot => option(Fe),
        /*
         * Digital signatures
         */
        Core::CheckSigVerify | Core::Bip0340Verify => AliasedType::unit(),
        /*
         * Bitcoin (without primitives)
         */
        Core::ParseLock => either(Height, Time),
        Core::ParseSequence => option(either(Distance, Duration)),
        Core::TapdataInit => Ctx8.into(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use simplicity::jet::{Core, Jet};

    #[test]
    fn compatible_source_type() {
        for jet in Core::ALL {
            let resolved_ty = ResolvedType::tuple(
                jet.source_type()
                    .into_iter()
                    .map(|t| t.resolve_builtin().unwrap()),
            );
            let structural_ty = StructuralType::from(&resolved_ty);
            let simplicity_ty = jet.source_ty().to_final();

            println!("{jet}");
            assert_eq!(structural_ty.as_ref(), simplicity_ty.as_ref());
        }
    }

    #[test]
    fn compatible_target_type() {
        for jet in Core::ALL {
            let resolved_ty = jet.target_type().resolve_builtin().unwrap();
            let structural_ty = StructuralType::from(&resolved_ty);
            let simplicity_ty = jet.target_ty().to_final();

            println!("{jet}");
            assert_eq!(structural_ty.as_ref(), simplicity_ty.as_ref());
        }
    }
}
