use crate::simplicity::jet::Elements;
use std::fmt;

#[rustfmt::skip]
pub fn documentation(jet: Elements) -> &'static str {
    match jet {
        // Multi-bit logic
        Elements::All8  => "Check if the value is [`u8::MAX`].",
        Elements::All16 => "Check if the value is [`u16::MAX`].",
        Elements::All32 => "Check if the value is [`u32::MAX`].",
        Elements::All64 => "Check if the value is [`u64::MAX`].",
        Elements::And1  => "Bitwise AND of two 1-bit values.",
        Elements::And8  => "Bitwise AND of two 8-bit values.",
        Elements::And16 => "Bitwise AND of two 16-bit values.",
        Elements::And32 => "Bitwise AND of two 32-bit values",
        Elements::And64 => "Bitwise AND of two 64-bit values",
        Elements::Ch1  => "Bitwise CHOICE of a bit and two 1-bit values.  If the bit is true, then take the first value, else take the second value.",
        Elements::Ch8  => "Bitwise CHOICE of a bit and two 8-bit values.  If the bit is true, then take the first value, else take the second value.",
        Elements::Ch16 => "Bitwise CHOICE of a bit and two 16-bit values. If the bit is true, then take the first value, else take the second value.",
        Elements::Ch32 => "Bitwise CHOICE of a bit and two 32-bit values. If the bit is true, then take the first value, else take the second value.",
        Elements::Ch64 => "Bitwise CHOICE of a bit and two 64-bit values. If the bit is true, then take the first value, else take the second value.",
        Elements::Complement1  => "Bitwise NOT of a 1-bit  value.",
        Elements::Complement8  => "Bitwise NOT of an 8-bit value.",
        Elements::Complement16 => "Bitwise NOT of a 16-bit value.",
        Elements::Complement32 => "Bitwise NOT of a 32-bit value.",
        Elements::Complement64 => "Bitwise NOT of a 64-bit value.",
        Elements::Eq1   => "Check if two 1-bit values are equal.",
        Elements::Eq8   => "Check if two 8-bit values are equal.",
        Elements::Eq16  => "Check if two 16-bit values are equal.",
        Elements::Eq32  => "Check if two 32-bit values are equal.",
        Elements::Eq64  => "Check if two 64-bit values are equal.",
        Elements::Eq256 => "Check if two 256-bit values are equal.",
        Elements::FullLeftShift8_1    => "Helper for left-shifting  bits. The bits are shifted from a 1-bit  value into a 8-bit  value. Return the shifted value and the 1  bit  that was  shifted out.",
        Elements::FullLeftShift8_2    => "Helper for left-shifting  bits. The bits are shifted from a 2-bit  value into a 8-bit  value. Return the shifted value and the 2  bits that were shifted out.",
        Elements::FullLeftShift8_4    => "Helper for left-shifting  bits. The bits are shifted from a 4-bit  value into a 8-bit  value. Return the shifted value and the 4  bits that were shifted out.",
        Elements::FullLeftShift16_1   => "Helper for left-shifting  bits. The bits are shifted from a 1-bit  value into a 16-bit value. Return the shifted value and the 1  bit  that was  shifted out.",
        Elements::FullLeftShift16_2   => "Helper for left-shifting  bits. The bits are shifted from a 2-bit  value into a 16-bit value. Return the shifted value and the 2  bits that were shifted out.",
        Elements::FullLeftShift16_4   => "Helper for left-shifting  bits. The bits are shifted from a 4-bit  value into a 16-bit value. Return the shifted value and the 4  bits that were shifted out.",
        Elements::FullLeftShift16_8   => "Helper for left-shifting  bits. The bits are shifted from a 8-bit  value into a 16-bit value. Return the shifted value and the 8  bits that were shifted out.",
        Elements::FullLeftShift32_1   => "Helper for left-shifting  bits. The bits are shifted from a 1-bit  value into a 32-bit value. Return the shifted value and the 1  bit  that was  shifted out.",
        Elements::FullLeftShift32_2   => "Helper for left-shifting  bits. The bits are shifted from a 2-bit  value into a 32-bit value. Return the shifted value and the 2  bits that were shifted out.",
        Elements::FullLeftShift32_4   => "Helper for left-shifting  bits. The bits are shifted from a 4-bit  value into a 32-bit value. Return the shifted value and the 4  bits that were shifted out.",
        Elements::FullLeftShift32_8   => "Helper for left-shifting  bits. The bits are shifted from a 8-bit  value into a 32-bit value. Return the shifted value and the 8  bits that were shifted out.",
        Elements::FullLeftShift32_16  => "Helper for left-shifting  bits. The bits are shifted from a 16-bit value into a 32-bit value. Return the shifted value and the 16 bits that were shifted out.",
        Elements::FullLeftShift64_1   => "Helper for left-shifting  bits. The bits are shifted from a 1-bit  value into a 64-bit value. Return the shifted value and the 1  bit  that was  shifted out.",
        Elements::FullLeftShift64_2   => "Helper for left-shifting  bits. The bits are shifted from a 2-bit  value into a 64-bit value. Return the shifted value and the 2  bits that were shifted out.",
        Elements::FullLeftShift64_4   => "Helper for left-shifting  bits. The bits are shifted from a 4-bit  value into a 64-bit value. Return the shifted value and the 4  bits that were shifted out.",
        Elements::FullLeftShift64_8   => "Helper for left-shifting  bits. The bits are shifted from a 8-bit  value into a 64-bit value. Return the shifted value and the 8  bits that were shifted out.",
        Elements::FullLeftShift64_16  => "Helper for left-shifting  bits. The bits are shifted from a 16-bit value into a 64-bit value. Return the shifted value and the 16 bits that were shifted out.",
        Elements::FullLeftShift64_32  => "Helper for left-shifting  bits. The bits are shifted from a 32-bit value into a 64-bit value. Return the shifted value and the 32 bits that were shifted out.",
        Elements::FullRightShift8_1   => "Helper for right-shifting bits. The bits are shifted from a 1-bit  value into a 8-bit  value. Return the shifted value and the 1  bit  that was  shifted out.",
        Elements::FullRightShift8_2   => "Helper for right-shifting bits. The bits are shifted from a 2-bit  value into a 8-bit  value. Return the shifted value and the 2  bits that were shifted out.",
        Elements::FullRightShift8_4   => "Helper for right-shifting bits. The bits are shifted from a 4-bit  value into a 8-bit  value. Return the shifted value and the 4  bits that were shifted out.",
        Elements::FullRightShift16_1  => "Helper for right-shifting bits. The bits are shifted from a 1-bit  value into a 16-bit value. Return the shifted value and the 1  bit  that was  shifted out.",
        Elements::FullRightShift16_2  => "Helper for right-shifting bits. The bits are shifted from a 2-bit  value into a 16-bit value. Return the shifted value and the 2  bits that were shifted out.",
        Elements::FullRightShift16_4  => "Helper for right-shifting bits. The bits are shifted from a 4-bit  value into a 16-bit value. Return the shifted value and the 4  bits that were shifted out.",
        Elements::FullRightShift16_8  => "Helper for right-shifting bits. The bits are shifted from a 8-bit  value into a 16-bit value. Return the shifted value and the 8  bits that were shifted out.",
        Elements::FullRightShift32_1  => "Helper for right-shifting bits. The bits are shifted from a 1-bit  value into a 32-bit value. Return the shifted value and the 1  bit  that was  shifted out.",
        Elements::FullRightShift32_2  => "Helper for right-shifting bits. The bits are shifted from a 2-bit  value into a 32-bit value. Return the shifted value and the 2  bits that were shifted out.",
        Elements::FullRightShift32_4  => "Helper for right-shifting bits. The bits are shifted from a 4-bit  value into a 32-bit value. Return the shifted value and the 4  bits that were shifted out.",
        Elements::FullRightShift32_8  => "Helper for right-shifting bits. The bits are shifted from a 8-bit  value into a 32-bit value. Return the shifted value and the 8  bits that were shifted out.",
        Elements::FullRightShift32_16 => "Helper for right-shifting bits. The bits are shifted from a 16-bit value into a 32-bit value. Return the shifted value and the 16 bits that were shifted out.",
        Elements::FullRightShift64_1  => "Helper for right-shifting bits. The bits are shifted from a 1-bit  value into a 64-bit value. Return the shifted value and the 1  bit  that was  shifted out.",
        Elements::FullRightShift64_2  => "Helper for right-shifting bits. The bits are shifted from a 2-bit  value into a 64-bit value. Return the shifted value and the 2  bits that were shifted out.",
        Elements::FullRightShift64_4  => "Helper for right-shifting bits. The bits are shifted from a 4-bit  value into a 64-bit value. Return the shifted value and the 4  bits that were shifted out.",
        Elements::FullRightShift64_8  => "Helper for right-shifting bits. The bits are shifted from a 8-bit  value into a 64-bit value. Return the shifted value and the 8  bits that were shifted out.",
        Elements::FullRightShift64_16 => "Helper for right-shifting bits. The bits are shifted from a 16-bit value into a 64-bit value. Return the shifted value and the 16 bits that were shifted out.",
        Elements::FullRightShift64_32 => "Helper for right-shifting bits. The bits are shifted from a 32-bit value into a 64-bit value. Return the shifted value and the 32 bits that were shifted out.",
        Elements::High1  => "Return `u1::MAX` = 1.",
        Elements::High8  => "Return [`u8::MAX`].",
        Elements::High16 => "Return [`u16::MAX`].",
        Elements::High32 => "Return [`u32::MAX`].",
        Elements::High64 => "Return [`u64::MAX`].",
        Elements::LeftExtend1_8    => "Extend a 1-bit  value to an 8-bit value by padding its left with the MSB.",
        Elements::LeftExtend1_16   => "Extend a 1-bit  value to a 16-bit value by padding its left with the MSB.",
        Elements::LeftExtend1_32   => "Extend a 1-bit  value to a 32-bit value by padding its left with the MSB.",
        Elements::LeftExtend1_64   => "Extend a 1-bit  value to a 64-bit value by padding its left with the MSB.",
        Elements::LeftExtend8_16   => "Extend an 8-bit value to a 16-bit value by padding its left with the MSB.",
        Elements::LeftExtend8_32   => "Extend an 8-bit value to a 32-bit value by padding its left with the MSB.",
        Elements::LeftExtend8_64   => "Extend an 8-bit value to a 64-bit value by padding its left with the MSB.",
        Elements::LeftExtend16_32  => "Extend a 16-bit value to a 32-bit value by padding its left with the MSB.",
        Elements::LeftExtend16_64  => "Extend a 16-bit value to a 64-bit value by padding its left with the MSB.",
        Elements::LeftExtend32_64  => "Extend a 16-bit value to a 64-bit value by padding its left with the MSB.",
        Elements::LeftPadHigh1_8   => "Extend a 1-bit  value to an 8-bit value by padding its left with ones.",
        Elements::LeftPadHigh1_16  => "Extend a 1-bit  value to a 16-bit value by padding its left with ones.",
        Elements::LeftPadHigh1_32  => "Extend a 1-bit  value to a 32-bit value by padding its left with ones.",
        Elements::LeftPadHigh1_64  => "Extend a 1-bit  value to a 64-bit value by padding its left with ones.",
        Elements::LeftPadHigh8_16  => "Extend an 8-bit value to a 16-bit value by padding its left with ones.",
        Elements::LeftPadHigh8_32  => "Extend an 8-bit value to a 32-bit value by padding its left with ones.",
        Elements::LeftPadHigh8_64  => "Extend a 1-bit  value to a 64-bit value by padding its left with ones.",
        Elements::LeftPadHigh16_32 => "Extend a 16-bit value to a 32-bit value by padding its left with ones.",
        Elements::LeftPadHigh16_64 => "Extend a 16-bit value to a 64-bit value by padding its left with ones.",
        Elements::LeftPadHigh32_64 => "Extend a 32-bit value to a 64-bit value by padding its left with ones.",
        Elements::LeftPadLow1_8    => "Extend a 1-bit  value to an 8-bit value by padding its left with zeroes.",
        Elements::LeftPadLow1_16   => "Extend a 1-bit  value to a 16-bit value by padding its left with zeroes.",
        Elements::LeftPadLow1_32   => "Extend a 1-bit  value to a 32-bit value by padding its left with zeroes.",
        Elements::LeftPadLow1_64   => "Extend a 1-bit  value to a 64-bit value by padding its left with zeroes.",
        Elements::LeftPadLow8_16   => "Extend an 8-bit value to a 16-bit value by padding its left with zeroes.",
        Elements::LeftPadLow8_32   => "Extend an 8-bit value to a 32-bit value by padding its left with zeroes.",
        Elements::LeftPadLow8_64   => "Extend an 8-bit value to a 64-bit value by padding its left with zeroes.",
        Elements::LeftPadLow16_32  => "Extend a 16-bit value to a 32-bit value by padding its left with zeroes.",
        Elements::LeftPadLow16_64  => "Extend a 16-bit value to a 64-bit value by padding its left with zeroes.",
        Elements::LeftPadLow32_64  => "Extend a 32-bit value to a 64-bit value by padding its left with zeroes.",
        Elements::LeftRotate8  => "Left-rotate an 8-bit value by the given amount.",
        Elements::LeftRotate16 => "Left-rotate a 16-bit value by the given amount.",
        Elements::LeftRotate32 => "Left-rotate a 32-bit value by the given amount.",
        Elements::LeftRotate64 => "Left-rotate a 64-bit value by the given amount.",
        Elements::LeftShift8      => "Left-shift an 8-bit value by the given amount. Bits are filled with zeroes.",
        Elements::LeftShift16     => "Left-shift a 16-bit value by the given amount. Bits are filled with zeroes.",
        Elements::LeftShift32     => "Left-shift a 32-bit value by the given amount. Bits are filled with zeroes.",
        Elements::LeftShift64     => "Left-shift a 64-bit value by the given amount. Bits are filled with zeroes.",
        Elements::LeftShiftWith8  => "Left-shift an 8-bit value by the given amount. Bits are filled with the given bit.",
        Elements::LeftShiftWith16 => "Left-shift a 16-bit value by the given amount. Bits are filled with the given bit.",
        Elements::LeftShiftWith32 => "Left-shift a 32-bit value by the given amount. Bits are filled with the given bit.",
        Elements::LeftShiftWith64 => "Left-shift a 64-bit value by the given amount. Bits are filled with the given bit.",
        Elements::Leftmost8_1   => "Return the most significant 1  bits of an 8-bit value.",
        Elements::Leftmost8_2   => "Return the most significant 1  bits of an 8-bit value.",
        Elements::Leftmost8_4   => "Return the most significant 1  bits of an 8-bit value.",
        Elements::Leftmost16_1  => "Return the most significant 1  bit  of a 16-bit value.",
        Elements::Leftmost16_2  => "Return the most significant 2  bits of a 16-bit value.",
        Elements::Leftmost16_4  => "Return the most significant 4  bits of a 16-bit value.",
        Elements::Leftmost16_8  => "Return the most significant 8  bits of a 16-bit value.",
        Elements::Leftmost32_1  => "Return the most significant 1  bit  of a 32-bit value.",
        Elements::Leftmost32_2  => "Return the most significant 2  bits of a 32-bit value.",
        Elements::Leftmost32_4  => "Return the most significant 4  bits of a 32-bit value.",
        Elements::Leftmost32_8  => "Return the most significant 8  bits of a 32-bit value.",
        Elements::Leftmost32_16 => "Return the most significant 16 bits of a 32-bit value.",
        Elements::Leftmost64_1  => "Return the most significant 1  bits of a 64-bit value.",
        Elements::Leftmost64_2  => "Return the most significant 2  bits of a 64-bit value.",
        Elements::Leftmost64_4  => "Return the most significant 4  bits of a 64-bit value.",
        Elements::Leftmost64_8  => "Return the most significant 8  bits of a 64-bit value.",
        Elements::Leftmost64_16 => "Return the most significant 16 bits of a 64-bit value.",
        Elements::Leftmost64_32 => "Return the most significant 32 bits of a 64-bit value.",
        Elements::Low1  => "Return `u1::MIN` = 1.",
        Elements::Low8  => "Return [`u8::MIN`].",
        Elements::Low16 => "Return [`u16::MIN`].",
        Elements::Low32 => "Return [`u32::MIN`].",
        Elements::Low64 => "Return [`u64::MIN`].",
        Elements::Maj1  => "Bitwise MAJORITY of three 1-bit values. The output bit is false if two or more input bits are false, and true otherwise.",
        Elements::Maj8  => "Bitwise MAJORITY of three 1-bit values. The output bit is false if two or more input bits are false, and true otherwise.",
        Elements::Maj16 => "Bitwise MAJORITY of three 1-bit values. The output bit is false if two or more input bits are false, and true otherwise.",
        Elements::Maj32 => "Bitwise MAJORITY of three 1-bit values. The output bit is false if two or more input bits are false, and true otherwise.",
        Elements::Maj64 => "Bitwise MAJORITY of three 1-bit values. The output bit is false if two or more input bits are false, and true otherwise.",
        Elements::Or1  => "Bitwise OR of two 1-bit values.",
        Elements::Or8  => "Bitwise OR of two 8-bit values.",
        Elements::Or16 => "Bitwise OR of two 16-bit values.",
        Elements::Or32 => "Bitwise OR of two 32-bit values.",
        Elements::Or64 => "Bitwise OR of two 64-bit values.",
        Elements::RightExtend8_16   => "Extend an 8-bit value to a 16-bit value by padding its right with the MSB.",
        Elements::RightExtend8_32   => "Extend an 8-bit value to a 32-bit value by padding its right with the MSB.",
        Elements::RightExtend8_64   => "Extend an 8-bit value to a 64-bit value by padding its right with the MSB.",
        Elements::RightExtend16_32  => "Extend a 16-bit value to a 32-bit value by padding its right with the MSB.",
        Elements::RightExtend16_64  => "Extend a 16-bit value to a 64-bit value by padding its right with the MSB.",
        Elements::RightExtend32_64  => "Extend a 16-bit value to a 64-bit value by padding its right with the MSB.",
        Elements::RightPadHigh1_8   => "Extend a 1-bit  value to an 8-bit value by padding its right with ones.",
        Elements::RightPadHigh1_16  => "Extend a 1-bit  value to a 16-bit value by padding its right with ones.",
        Elements::RightPadHigh1_32  => "Extend a 1-bit  value to a 32-bit value by padding its right with ones.",
        Elements::RightPadHigh1_64  => "Extend a 1-bit  value to a 64-bit value by padding its right with ones.",
        Elements::RightPadHigh8_16  => "Extend an 8-bit  value to a 16-bit value by padding its right with ones.",
        Elements::RightPadHigh8_32  => "Extend an 8-bit  value to a 32-bit value by padding its right with ones.",
        Elements::RightPadHigh8_64  => "Extend a 1-bit  value to a 64-bit value by padding its right with ones.",
        Elements::RightPadHigh16_32 => "Extend a 16-bit value to a 32-bit value by padding its right with ones.",
        Elements::RightPadHigh16_64 => "Extend a 16-bit value to a 64-bit value by padding its right with ones.",
        Elements::RightPadHigh32_64 => "Extend a 32-bit value to a 64-bit value by padding its right with ones.",
        Elements::RightPadLow1_8    => "Extend a 1-bit  value to an 8-bit value by padding its right with zeroes.",
        Elements::RightPadLow1_16   => "Extend a 1-bit  value to a 16-bit value by padding its right with zeroes.",
        Elements::RightPadLow1_32   => "Extend a 1-bit  value to a 32-bit value by padding its right with zeroes.",
        Elements::RightPadLow1_64   => "Extend a 1-bit  value to a 64-bit value by padding its right with zeroes.",
        Elements::RightPadLow8_16   => "Extend an 8-bit value to a 16-bit value by padding its right with zeroes.",
        Elements::RightPadLow8_32   => "Extend an 8-bit value to a 32-bit value by padding its right with zeroes.",
        Elements::RightPadLow8_64   => "Extend an 8-bit value to a 64-bit value by padding its right with zeroes.",
        Elements::RightPadLow16_32  => "Extend a 16-bit value to a 32-bit value by padding its right with zeroes.",
        Elements::RightPadLow16_64  => "Extend a 16-bit value to a 64-bit value by padding its right with zeroes.",
        Elements::RightPadLow32_64  => "Extend a 32-bit value to a 64-bit value by padding its right with zeroes.",
        Elements::RightRotate8  => "Right-rotate an 8-bit value by the given amount.",
        Elements::RightRotate16 => "Right-rotate a 16-bit value by the given amount.",
        Elements::RightRotate32 => "Right-rotate a 32-bit value by the given amount.",
        Elements::RightRotate64 => "Right-rotate a 64-bit value by the given amount.",
        Elements::RightShift8      => "Right-shift an 8-bit value by the given amount. Bits are filled with zeroes.",
        Elements::RightShift16     => "Right-shift a 16-bit value by the given amount. Bits are filled with zeroes.",
        Elements::RightShift32     => "Right-shift a 32-bit value by the given amount. Bits are filled with zeroes.",
        Elements::RightShift64     => "Right-shift a 64-bit value by the given amount. Bits are filled with zeroes.",
        Elements::RightShiftWith8  => "Right-shift an 8-bit value by the given amount. Bits are filled with the given bit.",
        Elements::RightShiftWith16 => "Right-shift a 16-bit value by the given amount. Bits are filled with the given bit.",
        Elements::RightShiftWith32 => "Right-shift a 32-bit value by the given amount. Bits are filled with the given bit.",
        Elements::RightShiftWith64 => "Right-shift a 64-bit value by the given amount. Bits are filled with the given bit.",
        Elements::Rightmost8_1   => "Return the least significant 1  bits of an 8-bit value.",
        Elements::Rightmost8_2   => "Return the least significant 1  bits of an 8-bit value.",
        Elements::Rightmost8_4   => "Return the least significant 1  bits of an 8-bit value.",
        Elements::Rightmost16_1  => "Return the least significant 1  bit  of a 16-bit value.",
        Elements::Rightmost16_2  => "Return the least significant 2  bits of a 16-bit value.",
        Elements::Rightmost16_4  => "Return the least significant 4  bits of a 16-bit value.",
        Elements::Rightmost16_8  => "Return the least significant 8  bits of a 16-bit value.",
        Elements::Rightmost32_1  => "Return the least significant 1  bit  of a 32-bit value.",
        Elements::Rightmost32_2  => "Return the least significant 2  bits of a 32-bit value.",
        Elements::Rightmost32_4  => "Return the least significant 4  bits of a 32-bit value.",
        Elements::Rightmost32_8  => "Return the least significant 8  bits of a 32-bit value.",
        Elements::Rightmost32_16 => "Return the least significant 16 bits of a 32-bit value.",
        Elements::Rightmost64_1  => "Return the least significant 1  bits of a 64-bit value.",
        Elements::Rightmost64_2  => "Return the least significant 2  bits of a 64-bit value.",
        Elements::Rightmost64_4  => "Return the least significant 4  bits of a 64-bit value.",
        Elements::Rightmost64_8  => "Return the least significant 8  bits of a 64-bit value.",
        Elements::Rightmost64_16 => "Return the least significant 16 bits of a 64-bit value.",
        Elements::Rightmost64_32 => "Return the least significant 32 bits of a 64-bit value.",
        Elements::Some1  => "Check if a 1-bit  value is nonzero.",
        Elements::Some8  => "Check if an 8-bit value is nonzero.",
        Elements::Some16 => "Check if a 16-bit value is nonzero.",
        Elements::Some32 => "Check if a 32-bit value is nonzero.",
        Elements::Some64 => "Check if a 64-bit value is nonzero.",
        Elements::Verify => r#"Assert that a bit is true.

## Panics
The assertion fails."#,
        Elements::Xor1  => "Bitwise XOR of two 1-bit  values.",
        Elements::Xor8  => "Bitwise XOR of two 8-bit  values.",
        Elements::Xor16 => "Bitwise XOR of two 16-bit values.",
        Elements::Xor32 => "Bitwise XOR of two 32-bit values.",
        Elements::Xor64 => "Bitwise XOR of two 64-bit values.",
        Elements::XorXor1  => "Bitwise XOR of three 1-bit  values.",
        Elements::XorXor8  => "Bitwise XOR of three 8-bit  values.",
        Elements::XorXor16 => "Bitwise XOR of three 16-bit values.",
        Elements::XorXor32 => "Bitwise XOR of three 32-bit values.",
        Elements::XorXor64 => "Bitwise XOR of three 64-bit values.",
        // Arithmetic
        Elements::Add8
        | Elements::Add16
        | Elements::Add32
        | Elements::Add64 => "Add two integers and return the carry.",
        Elements::Decrement8
        | Elements::Decrement16
        | Elements::Decrement32
        | Elements::Decrement64 => "Decrement an integer by one and return the borrow bit.",
        Elements::DivMod8
        | Elements::DivMod16
        | Elements::DivMod32
        | Elements::DivMod64 => "Divide the first integer by the second integer, and return the remainder.",
        Elements::DivMod128_64 => r#"Divide the 128-bit integer `a` by the 64-bit integer `b`.
Return a tuple of the quotient `q` and the remainer `r`.

Use this jet to recursively define wide integer divisions.

## Preconditions
1. `q` < 2^64
2. 2^63 ≤ `b`

Return `(u64::MAX, u64::MAX)` when the preconditions are not satisfied."#,
        Elements::Divide8
        | Elements::Divide16
        | Elements::Divide32
        | Elements::Divide64 => "Divide the first integer by the second integer.",
        Elements::Divides8
        | Elements::Divides16
        | Elements::Divides32
        | Elements::Divides64 => "Check if the first integer is divisible by the second integer.",
        Elements::FullAdd8
        | Elements::FullAdd16
        | Elements::FullAdd32
        | Elements::FullAdd64 => "Add two integers. Take a carry-in and return a carry-out.",
        Elements::FullDecrement8
        | Elements::FullDecrement16
        | Elements::FullDecrement32
        | Elements::FullDecrement64 => "Decrement an integer by one. Take a borrow-in and return a borrow-out.",
        Elements::FullIncrement8
        | Elements::FullIncrement16
        | Elements::FullIncrement32
        | Elements::FullIncrement64 => "Increment an integer by one. Take a carry-in and return a carry-out.",
        Elements::FullMultiply8
        | Elements::FullMultiply16
        | Elements::FullMultiply32
        | Elements::FullMultiply64 => "Helper for multiplying integers. Take the product of the first pair of integers and add the sum of the second pair.",
        Elements::FullSubtract8
        | Elements::FullSubtract16
        | Elements::FullSubtract32
        | Elements::FullSubtract64 => "Subtract the second integer from the first integer. Take a borrow-in and return a borrow-out.",
        Elements::Increment8
        | Elements::Increment16
        | Elements::Increment32
        | Elements::Increment64 => "Increment an integer by one and return the carry.",
        Elements::IsOne8
        | Elements::IsOne16
        | Elements::IsOne32
        | Elements::IsOne64  => "Check if an integer is one.",
        Elements::IsZero8
        | Elements::IsZero16
        | Elements::IsZero32
        | Elements::IsZero64 => "Check if an integer is zero.",
        Elements::Le8
        | Elements::Le16
        | Elements::Le32
        | Elements::Le64 => "Check if an integer is less than or equal to another integer.",
        Elements::Lt8
        | Elements::Lt16
        | Elements::Lt32
        | Elements::Lt64 => "Check if an integer is less than another integer.",
        Elements::Max8
        | Elements::Max16
        | Elements::Max32
        | Elements::Max64 => "Return the bigger of two integers.",
        Elements::Median8
        | Elements::Median16
        | Elements::Median32
        | Elements::Median64 => "Return the median of three integers.",
        Elements::Min8
        | Elements::Min16
        | Elements::Min32
        | Elements::Min64 => "Return the smaller of two integers.",
        Elements::Modulo8
        |Elements::Modulo16
        |Elements::Modulo32
        |Elements::Modulo64 => "Compute the remainder after dividing both integers.",
        Elements::Multiply8  => "Multiply two integers. The output is a 16-bit integer.",
        Elements::Multiply16 => "Multiply two integers. The output is a 32-bit integer.",
        Elements::Multiply32 => "Multiply two integers. The output is a 64-bit integer.",
        Elements::Multiply64 => "Multiply two integers. The output is a 128-bit integer.",
        Elements::Negate8  => "Negate the integer (modulo 2⁸)  and return the borrow bit.",
        Elements::Negate16 => "Negate the integer (modulo 2¹⁶) and return the borrow bit.",
        Elements::Negate32 => "Negate the integer (modulo 2³²) and return the borrow bit.",
        Elements::Negate64 => "Negate the integer (modulo 2⁶⁴) and return the borrow bit.",
        Elements::One8  => "Return 1 as an 8-bit integer.",
        Elements::One16 => "Return 1 as a 16-bit integer.",
        Elements::One32 => "Return 1 as a 32-bit integer.",
        Elements::One64 => "Return 1 as a 64-bit integer.",
        Elements::Subtract8
        | Elements::Subtract16
        | Elements::Subtract32
        | Elements::Subtract64 => "Subtract the second integer from the first integer, and return the borrow bit.",
        // Hash functions
        Elements::Sha256Block => "Update the given 256-bit midstate by running the SHA256 block compression function, using the given 512-bit block.",
        Elements::Sha256Ctx8Add1   => "Add 1   byte  to the SHA256 hash engine.",
        Elements::Sha256Ctx8Add2   => "Add 2   bytes to the SHA256 hash engine.",
        Elements::Sha256Ctx8Add4   => "Add 4   bytes to the SHA256 hash engine.",
        Elements::Sha256Ctx8Add8   => "Add 8   bytes to the SHA256 hash engine.",
        Elements::Sha256Ctx8Add16  => "Add 16  bytes to the SHA256 hash engine.",
        Elements::Sha256Ctx8Add32  => "Add 32  bytes to the SHA256 hash engine.",
        Elements::Sha256Ctx8Add64  => "Add 64  bytes to the SHA256 hash engine.",
        Elements::Sha256Ctx8Add128 => "Add 128 bytes to the SHA256 hash engine.",
        Elements::Sha256Ctx8Add256 => "Add 256 bytes to the SHA256 hash engine.",
        Elements::Sha256Ctx8Add512 => "Add 512 bytes to the SHA256 hash engine.",
        Elements::Sha256Ctx8AddBuffer511 => "Add a list of less than 512 bytes to the SHA256 hash engine.",
        Elements::Sha256Ctx8Finalize => "Produce a hash from the current state of the SHA256 hash engine.",
        Elements::Sha256Ctx8Init => "Initialize a default SHA256 hash engine.",
        Elements::Sha256Iv => "Return the SHA256 initial value.",
        // Elliptic curve functions
        Elements::Decompress => r#"Decompress a point into affine coordinates.

- Return `None` if the x-coordinate is not on the curve.
- Return `Some(ge)` even if the x-coordinate is not normalized."#,
        Elements::FeAdd => "Add two field elements.",
        Elements::FeInvert => "Compute the modular inverse of a field element.",
        Elements::FeIsOdd => "Check if the canonical representative of the field element is odd.",
        Elements::FeIsZero => "Check if the field element represents zero.",
        Elements::FeMultiply => "Multiply two field elements.",
        Elements::FeMultiplyBeta => "Multiply a field element by the canonical primitive cube root of unity (beta).",
        Elements::FeNegate => "Negate a field element.",
        Elements::FeNormalize => "Return the canonical representation of a field element.",
        Elements::FeSquare => "Square a field element.",
        Elements::FeSquareRoot => "Compute the modular square root of a field element if it exists.",
        Elements::GeIsOnCurve
        | Elements::GejIsOnCurve => "Check if the given point satisfies the curve equation y² = x³ + 7.",
        Elements::GeNegate
        | Elements::GejNegate => "Negate a point.",
        Elements::GejAdd => "Add two points.",
        Elements::GejDouble => "Double a point. If the result is the point at infinity, it is returned in canonical form.",
        Elements::GejEquiv => "Check if two points represent the same point.",
        Elements::GejGeAdd => "Add two points. If the result is the point at infinity, it is returned in canonical form.",
        Elements::GejGeAddEx => "Add two points. Also return the ration of the `a`s z-coordinate and the result's z-coordinate. If the result is the point at infinity, it is returned in canonical form.",
        Elements::GejGeEquiv => "Check if two points represent the same point.",
        Elements::GejInfinity => "Return the canonical representation of the point at infinity.",
        Elements::GejIsInfinity => "Check if the point represents infinity.",
        Elements::GejNormalize => "Convert the point into affine coordinates with canonical field representatives. If the result is the point at infinity, it is returned in canonical form.",
        Elements::GejRescale => "Change the representatives of a point by multiplying the z-coefficient by the given value.",
        Elements::GejXEquiv => "Check if the point represents an affine point with the given x-coordinate.",
        Elements::GejYIsOdd => "Check if the point represents an affine point with odd y-coordinate.",
        Elements::Generate => "Multiply the generator point with the given scalar.",
        Elements::LinearCombination1 => "Compute the linear combination `b * a + c * g` for point `b` and scalars `a` and `c`, where `g` is the generator point.",
        Elements::LinearVerify1 => r#"Assert that a point `b` is equal to the linear combination `a.0 * a.1 + a.2 * g`, where `g` is the generator point.

## Panics
The assertion fails."#,
        Elements::PointVerify1 => r#"Assert that a point `b` is equal to the linear combination `a.0 * a.1 + a.2 * g`, where `g` is the generator point.

## Panics
- The assertion fails.
- Fails if the points cannot be decompressed."#,
        Elements::ScalarAdd => "Add two scalars.",
        Elements::ScalarInvert => "Compute the modular inverse of a scalar.",
        Elements::ScalarIsZero => "Check if the scalar represents zero.",
        Elements::ScalarMultiply => "Multiply two scalars.",
        Elements::ScalarMultiplyLambda => "Multiply a scalar with the canonical primitive cube of unity (lambda)",
        Elements::ScalarNegate => "Negate a scalar.",
        Elements::ScalarNormalize => "Return the canonical representation of the scalar.",
        Elements::ScalarSquare => "Square a scalar.",
        Elements::Scale => "Multiply a point by a scalar.",
        Elements::HashToCurve => r#"A cryptographic hash function that results in a point on the secp256k1 curve.

This matches the hash function used to map asset IDs to asset commitments."#,
        Elements::Swu => r#"Algebraically distribute a field element over the secp256k1 curve as defined in
["Indifferentiable Hashing to Barreto-Naehrig Curves" by Pierre-Alain Fouque, Mehdi Tibouchi](https://inria.hal.science/hal-01094321/file/FT12.pdf).

While this by itself is not a cryptographic hash function, it can be used as a subroutine
in a [`hash_to_curve`] function. However, the distribution only approaches uniformity when it is called twice."#,
        // Digital Signatures
        Elements::Bip0340Verify => r#"Assert that a Schnorr signature matches a public key and message.

## Panics
The assertion fails."#,
        Elements::CheckSigVerify => r#"Assert that a Schnorr signature matches a public key and message, using a custom sighash mode.

## Panics
The assertion fails.

## Safety
This jet should not be used directly."#,
        // Bitcoin (without primitives)
        Elements::ParseLock => "Parse an integer as a consensus-encoded Bitcoin lock time.",
        Elements::ParseSequence => "Parse an integer as a consensus-encoded Bitcoin sequence number.",
        Elements::TapdataInit => r#"Create a SHA256 context, initialized with a "TapData" tag."#,
        // Signature hash modes
        Elements::AnnexHash => r#"Continue a SHA256 hash with an optional hash by appending the following:
- If there is no hash, then the byte `0x00`.
- If there is a hash, then the byte `0x01` followed by the given hash (32 bytes)."#,
        Elements::AssetAmountHash => "Continue a SHA256 hash with the serialization of a confidential asset followed by the serialization of a amount.",
        Elements::BuildTapbranch => r#"Return the SHA256 hash of the following:
- The hash of the ASCII string `TapBranch/elements` (32 bytes).
- The lexicographically smaller of the two inputs (32 bytes).
- The hash of the ASCII string `TapBranch/elements` again (32 bytes).
- The lexicographically larger of the two inputs (32 bytes).

This builds a taproot from two branches."#,
        Elements::BuildTapleafSimplicity => r#"Return the SHA256 hash of the following:
- The hash of the ASCII string `TapLeaf/elements` (32 bytes).
- The hash of the ASCII string `TapLeaf/elements` again (32 bytes).
- The Simplicity leaf version `0xbe` (1 byte).
- The byte `0x20` (1 byte).
- The input CMR (32 bytes).

This builds a tapleaf hash for a Simplicity program."#,
        Elements::BuildTaptweak => r#"Implementation of `taproot_tweak_pubkey` from BIP-0341.

## Panics
1. The input x-only public key is off curve or exceeds the field size.
2. The internal hash value `t` exceeds the secp256k1 group order.
3. The generated tweaked point is infinity, and thus has no valid x-only public key.

Note that situations 2 and 3 are cryptographically impossible to occur."#,
        Elements::InputAmountsHash => "Return the SHA256 hash of the serialization of each input UTXO's asset and amount fields.",
        Elements::InputAnnexesHash => r#"Return the SHA256 hash of the concatenation of the following for every input:
- If the input has no annex, or isn't a taproot spend, then the byte `0x00`.
- If the input has an annex, then the byte `0x01` followed by the SHA256 hash of the annex (32 bytes)."#,
        Elements::InputOutpointsHash => r#"Return the SHA256 hash of the concatenation of the following for every input:
- If the input is not a pegin, then the byte `0x00`.
- If the input is a pegin, then the byte `0x01` followed by the parent chain's genesis hash (32 bytes).
- The input's serialized previous transaction id (32 bytes).
- The input's previous transaction index in big endian format (4 bytes).

IMPORTANT: the index is serialized in big endian format rather than little endian format."#,
        Elements::InputScriptSigsHash => r#"Return the SHA256 hash of the concatenation of the SHA256 hash of each input's scriptSig.

Note that if an input's UTXO uses segwit, then it's scriptSig will necessarily be the empty string. In
such cases we still use the SHA256 hash of the empty string."#,
        Elements::InputScriptsHash => "Return the SHA256 hash of the concatenation of the SHA256 hash of each input UTXO's scriptPubKey.",
        Elements::InputSequencesHash => r#"Return the SHA256 hash of the concatenation of the following for every input:
- The input's sequence number in big endian format (4 bytes).

IMPORTANT, the sequence number is serialized in big endian format rather than little endian format."#,
        Elements::InputUtxoHash => r#"Return the SHA256 hash of the following:
- The serialization of the input UTXO's asset and amount fields.
- The SHA256 hash of the input UTXO's scriptPubKey.

Return `None` if the input does not exist."#,
        Elements::InputUtxosHash => r#"Return the SHA256 hash of the following:
- The result of [`input_amounts_hash`] (32 bytes).
- The result of [`input_scripts_hash`] (32 bytes)."#,
        Elements::InputHash => r#"Return the SHA256 hash of the following:
- If the input is not a pegin, then the byte `0x00`.
- If the input is a pegin, then the byte `0x01` followed by the parent chain's genesis hash (32 bytes).
- The input's serialized previous transaction id (32 bytes).
- The input's previous transaction index in big endian format (4 bytes).
- The input's sequence number in big endian format (4 bytes).
- If the input has no annex, or isn't a taproot spend, then the byte `0x00`.
- If the input has an annex, then the byte `0x01` followed by the SHA256 hash of the annex (32 bytes).

Return `None` if the input does not exist."#,
        Elements::InputsHash => r#"Return the SHA256 hash of the following:
- The result of [`input_outpoints_hash`] (32 bytes).
- The result of [`input_sequences_hash`] (32 bytes).
- The result of [`input_annexes_hash`] (32 bytes)."#,
        Elements::IssuanceAssetAmountsHash => r#"Return the SHA256 hash of the concatenation of the following for every input:
- If the input has no issuance then two bytes `0x00 0x00`.
- If the input is has a new issuance then the byte `0x01` followed by a serialization of the calculated issued
asset id (32 bytes) followed by the serialization of the (possibly confidential) issued asset amount (9
bytes or 33 bytes).
- If the input is has a reissuance then the byte `0x01` followed by a serialization of the issued asset id
(32 bytes), followed by the serialization of the (possibly confidential) issued asset amount (9 bytes or
33 bytes).

IMPORTANT: If there is an issuance but there are no asset issued (i.e. the amount is null) we serialize
the vase as the explicit 0 amount, (i.e. `0x01 0x00 0x00 0x00 0x00 0x00 0x00 0x00 0x00`).

Note, the issuance asset id is serialized in the same format as an explicit asset id would be."#,
        Elements::IssuanceBlindingEntropyHash => r#"Return the SHA256 hash of the concatenation of the following for every input:
- If the input has no issuance then the byte `0x00`.
- If the input is has a new issuance then the byte `0x01` followed by 32 `0x00` bytes and the new issuance's
contract hash field (32 bytes).
- If the input is has reissuance then the byte `0x01` followed by a serializaiton of the reissuance's blinding
nonce field (32 bytes) and the reissuance's entropy field (32 bytes).

Note that if the issuance is a new issuance then the blinding nonce field is 32 `0x00` bytes and new issuance's
contract hash."#,
        Elements::IssuanceRangeProofsHash => r#"Return the SHA256 hash of the concatenation of the following for every input:
- The SHA256 hash of the range proof of the input's issuance asset amount (32 bytes).
- The SHA256 hash of the range proof of the input's issuance token amount (32 bytes).

Note that each the range proof is considered to be the empty string in the case there is no issuance, or if the
asset or token amount doesn't exist (i.e is null). The SHA256 hash of the empty string is still used in these
cases."#,
        Elements::IssuanceTokenAmountsHash => r#"Return the SHA256 hash of the concatenation of the following for every input:
- If the input has no issuance then two bytes `0x00 0x00`.
- If the input is has a new issuance then the byte `0x01` followed by a serialization of the calculated issued
token id (32 bytes) followed by the serialization of the (possibly confidential) issued token amount (9
bytes or 33 bytes).
- If the input is has a reissuance then the byte `0x01` followed by a serialization of the issued token id
(32 bytes), followed by the serialization of the explicit 0 amount (i.e `0x01 0x00 0x00 0x00 0x00 0x00 0x00 0x00 0x00`) (9 bytes).

IMPORTANT: If there is an issuance but there are no tokens issued (i.e. the amount is null) we serialize
the vase as the explicit 0 amount, (i.e. `0x01 0x00 0x00 0x00 0x00 0x00 0x00 0x00 0x00`).

Note, the issuance token id is serialized in the same format as an explicit asset id would be."#,
        Elements::IssuanceHash => r#"Return the SHA256 hash of the following:
1. The asset issuance:
    - If the input has no issuance then two bytes `0x00 0x00`.
    - If the input is has a new issuance then the byte `0x01` followed by a serialization of the calculated issued
    asset id (32 bytes) followed by the serialization of the (possibly confidential) issued asset amount (9 bytes or 33 bytes).
    - If the input is has a reissuance then the byte `0x01` followed by a serialization of the issued asset id
    (32 bytes), followed by the serialization of the (possibly confidential) issued asset amount (9 bytes or 33 bytes).
2. The token issuance:
    - If the input has no issuance then two bytes `0x00 0x00`.
    - If the input is has a new issuance then the byte `0x01` followed by a serialization of the calculated issued
    token id (32 bytes) followed by the serialization of the (possibly confidential) issued token amount (9 bytes or 33 bytes).
    - If the input is has a reissuance then the byte `0x01` followed by a serialization of the issued token id (32 bytes),
    followed by the serialization of the explicit 0 amount (i.e `0x01 0x00 0x00 0x00 0x00 0x00 0x00 0x00 0x00`) (9 bytes).
3. The range proofs:
    - The SHA256 hash of the range proof of the input's issuance asset amount (32 bytes).
    - The SHA256 hash of the range proof of the input's issuance token amount (32 bytes).
4. The blinding entropy:
    - If the input has no issuance then the byte `0x00`.
    - If the input is has a new issuance then the byte `0x01` followed by 32 `0x00` bytes and the new issuance's
    contract hash field (32 bytes).
    - If the input is has reissuance then the byte `0x01` followed by a serializaiton of the reissuance's blinding
    nonce field (32 bytes) and the reissuance's entropy field (32 bytes).

Return `None` if the input does not exist."#,
        Elements::IssuancesHash => r#"Return the SHA256 hash of the following:
- The result of [`issuance_asset_amounts_hash`] (32 bytes).
- The result of [`issuance_token_amounts_hash`] (32 bytes).
- The result of [`issuance_range_proofs_hash`] (32 bytes).
- The result of [`issuance_blinding_entropy_hash`] (32 bytes)."#,
        Elements::NonceHash => "Continue the SHA256 hash with the serialization of an optional nonce.",
        Elements::OutpointHash => r#"Continue the SHA256 hash with an optional pegin and an outpoint by appending the following:
- If the input is not a pegin, then the byte `0x00`.
- If the input is a pegin, then the byte `0x01` followed by the given parent genesis hash (32 bytes).
- The input's previous transaction id (32 bytes).
- The input's previous transaction index in big endian format (4 bytes)."#,
        Elements::OutputAmountsHash => "Return the SHA256 hash of the serialization of each output's asset and amount fields.",
        Elements::OutputNoncesHash => "Return the SHA256 hash of the serialization of each output's nonce field.",
        Elements::OutputRangeProofsHash => r#"Return the SHA256 hash of the concatenation of the SHA256 hash of each output's range proof.

Note that if the output's amount is explicit then the range proof is considered the empty string."#,
        Elements::OutputScriptsHash => "Return the SHA256 hash of the concatenation of the SHA256 hash of each output's scriptPubKey.",
        Elements::OutputSurjectionProofsHash => r#"Return the SHA256 hash of the concatenation of the SHA256 hash of each output's surjection proof.

Note that if the output's asset is explicit then the surjection proof is considered the empty string."#,
        Elements::OutputHash => r#"Return the SHA256 hash of the following:
- The serialization of the output's asset and amount fields.
- The serialization of the output's nonce field.
- The SHA256 hash of the output's scriptPubKey.
- The SHA256 hash of the output's range proof.

Return `None` if the output does not exist.

Note: the result of [`output_surjection_proofs_hash`] is specifically excluded because surjection proofs are dependent on the inputs as well as the output."#,
        Elements::OutputsHash => r#"Return the SHA256 hash of the following:
- The result of [`output_amounts_hash`] (32 bytes).
- The result of [`output_nonces_hash`] (32 bytes).
- The result of [`output_scripts_hash`] (32 bytes).
- The result of [`output_range_proofs_hash`] (32 bytes).

Note: the result of [`output_surjection_proofs_hash`] is specifically excluded because surjection proofs are dependent on the inputs as well as the output. See also [`tx_hash`]."#,
        Elements::SigAllHash => r#"Return the SHA256 hash of the following:
- The result of [`genesis_block_hash`] (32 bytes).
- The result of [`genesis_block_hash`] again (32 bytes).
- The result of [`tx_hash`] (32 bytes).
- The result of [`tap_env_hash`] (32 bytes).
- The result of [`current_index`] (Note: this is in big endian format) (4 bytes).

Note: the two copies of the [`genesis_block_hash`] values effectively makes this result a BIP-340 style tagged hash."#,
        Elements::TapEnvHash => r#"Return the SHA256 hash of the following:
- The result of [`tapleaf_hash`] (32 bytes).
- The result of [`tappath_hash`] (32 bytes).
- The result of [`internal_key`] (32 bytes)."#,
        Elements::TapleafHash => r#"Return the SHA256 hash of the following:
- The hash of the ASCII string `TapLeaf/elements` (32 bytes).
- The hash of the ASCII string `TapLeaf/elements` again (32 bytes).
- The result of [`tapleaf_version`] (1 byte).
- The byte `0x20` (1 byte).
- The result of [`script_cmr`] (32 bytes).

Note: this matches Element's modified BIP-0341 definition of tapleaf hash."#,
        Elements::TappathHash => r#"Return a hash of the current input's control block excluding the leaf version and the taproot internal key.

Using the notation of BIP-0341, it returns the SHA256 hash of c[33: 33 + 32m]."#,
        Elements::TxHash => r#"Return the SHA256 hash of the following:
- The result of [`version`] (Note: this is in big endian format) (4 bytes).
- The result of [`tx_lock_time`] (Note: this is in big endian format) (4 bytes).
- The result of [`inputs_hash`] (32 bytes).
- The result of [`outputs_hash`] (32 bytes).
- The result of [`issuances_hash`] (32 bytes).
- The result of [`output_surjection_proofs_hash`] (32 bytes).
- The result of [`input_utxos_hash`] (32 bytes)."#,
        // Time locks
        Elements::CheckLockDistance => r#"Assert that the value returned by [`tx_lock_distance`] is greater than or equal to the given value.

## Panics
The assertion fails."#,
        Elements::CheckLockDuration => r#"Assert that the value returned by [`tx_lock_duration`] is greater than or equal to the given value.

## Panics
The assertion fails"#,
        Elements::CheckLockHeight   => r#"Assert that the value returned by [`tx_lock_height`]   is greater than or equal to the given value.

## Panics
The assertion fails."#,
        Elements::CheckLockTime     => r#"Assert that the value returned by [`tx_lock_time`]     is greater than or equal to the given value.

## Panics
The assertion fails."#,
        Elements::TxIsFinal => "Check if the sequence numbers of all transaction inputs are at their maximum value.",
        Elements::TxLockDistance => "If [`version`] returns 2 or greater, then return the greatest valid [`Distance`] value of any transaction input. Return zeroes otherwise.",
        Elements::TxLockDuration => "If [`version`] returns 2 or greater, then return the greatest valid [`Duration`] value of any transaction input. Return zeroes otherwise.",
        Elements::TxLockHeight => "If [`tx_is_final`] returns false, then try to parse the transaction's lock time as a [`Height`] value. Return zeroes otherwise.",
        Elements::TxLockTime   => "If [`tx_is_final`] returns false, then try to parse the transaction's lock time as a [`Time`] value. Return zeroes otherwise.",
        // Issuance
        Elements::CalculateAsset => "Calculate the issued asset id from a given entropy value.",
        Elements::CalculateConfidentialToken => "Calculate the reissuance token id from a given entropy value for assets with confidential issued amounts.",
        Elements::CalculateExplicitToken => "Calculate the reissuance token id from a given entropy value for assets with explicit issued amounts.",
        Elements::CalculateIssuanceEntropy => r#"Calculate the entropy value from a given outpoint and contract hash.

This entropy value is used to compute issued asset and token IDs."#,
        Elements::Issuance => r#"Return the kind of issuance of the input at the given index:
- Return `Some(Some(false))` if the input has new issuance.
- Return `Some(Some(true))` if the input as reissuance.
- Return `Some(None)` if the input has no issuance.
- Return `None` if the input does not exist."#,
        Elements::IssuanceAsset => r#"Return the ID of the issued asset of the input at the given index:
- Return `Some(Some(x))` if the input has issuance with asset id `x`.
- Return `Some(None)` if the input has no issuance.
- Return `None` if the input does not exist."#,
        Elements::IssuanceEntropy => r#"Return the issuance entropy of the input at the given index:
- Return `Some(Some(x))` if the input has reissuance with entropy `x` or if there is new issuance whose computed entropy is `x`.
- Return `Some(Some(x))` if the input has no issuance.
- Return `None` if the input does not exist."#,
        Elements::IssuanceToken => r#"Return the reissuance token of the input at the given index:
- Return `Some(Some(x))` if the input has issuance with the reissuance token ID `x`.
- Return `Some(None)` if the input has no issuance.
- Return `None` if the input does not exist."#,
        Elements::LbtcAsset => "Return the asset for Liquid Bitcoin.",
        // Transaction
        Elements::CurrentAmount => "Return the [`input_amount`] at the [`current_index`].",
        Elements::CurrentAnnexHash => "Return the [`input_annex_hash`] at th [`current_index`].",
        Elements::CurrentAsset => "Return the [`input_asset`] at the [`current_index`].",
        Elements::CurrentIndex => "Return the index of the current txin.",
        Elements::CurrentIssuanceAssetAmount => "Return the [`issuance_asset_amount`] at the [`current_index`].",
        Elements::CurrentIssuanceAssetProof  => "Return the [`issuance_asset_proof`]  at the [`current_index`].",
        Elements::CurrentIssuanceTokenAmount => "Return the [`issuance_token_amount`] at the [`current_index`].",
        Elements::CurrentIssuanceTokenProof  => "Return the [`issuance_token_proof`]  at the [`current_index`].",
        Elements::CurrentNewIssuanceContract => "Return the [`new_issuance_contract`] at the [`current_index`].",
        Elements::CurrentPegin => "Return the [`input_pegin`] at the [`current_index`].",
        Elements::CurrentPrevOutpoint => "Return the previous outpoint of the current txin.",
        Elements::CurrentReissuanceBlinding => "Return the [`reissuance_blinding`] at the [`current_index`].",
        Elements::CurrentReissuanceEntropy  => "Return the [`reissuance_entropy`]  at the [`current_index`].",
        Elements::CurrentScriptHash    => "Return the SHA256 hash of the scriptPubKey of the UTXO of the current txin.",
        Elements::CurrentScriptSigHash => r#"Return the SHA256 hash of the scriptSig of the current txin.

SegWit UTXOs enforce scriptSig to be the empty string. In such cases, we return the SHA256 hash of the empty string."#,
        Elements::CurrentSequence => r#"Return the nSequence of the current txin.

Use this jet to obtain the raw, encoded sequence number.
Use [`tx_lock_distance`] to obtain a relative block height, or [`tx_lock_duration`] to obtain a relative UNIX timestamp, in a safe manner."#,
        Elements::GenesisBlockHash => "Return the SHA256 hash of the genesis block.",
        Elements::InputAmount => r#"Return the asset id and the asset amount at the given input index.

Return `None` if the input does not exist."#,
        Elements::InputAnnexHash => r#"Return the SHA256 hash of the annex at the given input:
- Return `Some(Some(x))` if the input has an annex that hashes to `x`.
- Return `Some(None`) if the input has no annex.
- Return `None` if the input does not exist."#,
        Elements::InputAsset => r#"Return the asset id of the input at the given index.

Return `None` if the input does not exist."#,
        Elements::InputPegin => r#"Return the parent genesis block hash if the input at the given index is a peg-in.

- Return `Some(None)` if the input is not a peg-in.
- Return `None` if the input does not exist."#,
        Elements::InputPrevOutpoint => r#"Return the previous outpoint of the input at the given index.

Return `None` if the input does not exist."#,
        Elements::InputScriptHash => r#"Return the SHA256 hash of the scriptPubKey of the UTXO of the input at the given index.

Return `None` if the input does not exist."#,
        Elements::InputScriptSigHash => r#"Return the SHA256 hash of the scriptSigKey of the input at the given index.

Return `None` if the input does not exist.

SegWit UTXOs enforce scriptSig to be the empty string. In such cases, we return the SHA256 hash of the empty string."#,
        Elements::InputSequence => r#"Return the nSequence of the input at the given index.

Return `None` if the input does not exist."#,
        Elements::InternalKey => r#"Return the internal key of the current input.

We assume that Simplicity can be spent in Taproot outputs only, so there always exists an internal key."#,
        Elements::IssuanceAssetAmount => r#"Return the possibly confidential amount of the issuance if the input at the given index has an issuance.

- Return `Some(None)` if the input does not have an issuance.
- Return `None` if the input does not exist."#,
        Elements::IssuanceAssetProof  => r#"Return the SHA256 hash of the range proof for the amount of the issuance at the given input index.

- Return the hash of the empty string if the input does not have an issuance.
- Return `None` if the input does not exist."#,
        Elements::IssuanceTokenAmount => r#"Return the possibly confidential amount of the reissuance tokens if the input at the given index has an issuance.

- Return `Some(Some(Right(0)))` if the input is itself a reissuance.
- Return `Some(None)` if the input does not have an issuance.
- Return `None` if the input does not exist."#,
        Elements::IssuanceTokenProof  => r#"Return the SHA256 hash of the range proof for the amount of the reissuance tokens at the given input index.

- Return the hash of the empty string if the input does not have an issuance.
- Return `None` if the input does not exist."#,
        Elements::LockTime => "Return the lock time of the transaction.",
        Elements::NewIssuanceContract => r#"Return the contract hash for the new issuance at the given input index.

- Return `Some(None)` if the input does not have a new issuance.
- Return `None` if the input does not exist."#,
        Elements::NumInputs => "Return the number of inputs of the transaction.",
        Elements::NumOutputs => "Return the number of outputs of the transaction.",
        Elements::OutputAmount => r#"Return the asset amount of the output at the given index.

Return `None` if the output does not exist."#,
        Elements::OutputAsset => r#"Return the asset id of the output at the given index.

Return `None` if the output does not exist."#,
        Elements::OutputIsFee => r#"Check if the output at the given index is a fee output.

Return `None` if the output does not exist."#,
        Elements::OutputNonce => r#"Return the nonce of the output at the given index.

- Return `Some(None)` if the output does not have a nonce.
- Return `None` if the output does not exist."#,
        Elements::OutputNullDatum => r#"Return the `b`-th entry of a null data (`OP_RETURN`) output at index `a`.

- Return `Some(Some(Right(Right(x-1))))` if the entry is `OP_x` for `x` in the range 1..=16.
- Return `Some(Some(Right(Left(0))))` if the entry is `OP_1NEGATE`.
- Return `Some(Some(Right(Left(1))))` if the entry is `OP_RESERVED`.
- Return `Some(Some(Left((x, hash))))` if the entry is pushed data. `hash` is the SHA256 hash of the data pushed and `x` indicates how the data was pushed:
    - `x == 0` means the push was an immediate 0 to 75 bytes.
    - `x == 1` means the push was an `OP_PUSHDATA1`.
    - `x == 2` means the push was an `OP_PUSHDATA2`.
    - `x == 3` means the push was an `OP_PUSHDATA4`.
- Return `Some(None)` if the null data has fewer than `b` entries.
- Return `None` if the output is not a null data output.

Use this jet to read peg-out data from an output."#,
        Elements::OutputRangeProof => r#"Return the SHA256 hash of the range proof of the output at the given index.

Return `None` if the output does not exist."#,
        Elements::OutputScriptHash => r#"Return the SHA256 hash of the scriptPubKey of the output at the given index.

Return `None` if the output does not exist."#,
        Elements::OutputSurjectionProof => r#"Return the SHA256 hash of the surjection proof of the output at the given index.

Return `None` if the output does not exist."#,
        Elements::ReissuanceBlinding => r#"Return the blinding factor used for the reissuance at the given input index.

- Return `Some(None)` if the input does not have a reissuance.
- Return `None` if the input does not exist."#,
        Elements::ReissuanceEntropy => r#"Return the entropy used for the reissuance at the given input index.

- Return `Some(None)` if the input does not have a reissuance.
- Return `None` if the input does not exist."#,
        Elements::ScriptCMR => r#"Return the CMR of the Simplicity program in the current input.

This is the CMR of the currently executed Simplicity program."#,
        Elements::TapleafVersion => r#"Return the tap leaf version of the current input.

We assume that Simplicity can be spent in Taproot outputs only, so there always exists a tap leaf."#,
        Elements::Tappath => r#"Return the SHA256 hash of the tap path of the current input.

We assume that Simplicity can be spent in Taproot outputs only, so there always exists a tap path."#,
        Elements::TotalFee => r#"Return the total amount of fees paid to the given asset id.

Return zero for any asset without fees."#,
        Elements::TransactionId => "Return the transaction ID.",
        Elements::Version => "Return the version number of the transaction.",
    }
}

/// Category of an Elements jet.
#[derive(Copy, Clone, Eq, PartialEq)]
pub enum Category {
    MultiBitLogic,
    Arithmetic,
    HashFunctions,
    EllipticCurveFunctions,
    DigitalSignatures,
    BitcoinWithoutPrimitives,
    SignatureHashModes,
    TimeLocks,
    Issuance,
    Transaction,
}

impl fmt::Display for Category {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Category::MultiBitLogic => f.write_str("multi_bit_logic"),
            Category::Arithmetic => f.write_str("arithmetic"),
            Category::HashFunctions => f.write_str("hash_functions"),
            Category::EllipticCurveFunctions => f.write_str("elliptic_curve_functions"),
            Category::DigitalSignatures => f.write_str("digital_signatures"),
            Category::BitcoinWithoutPrimitives => f.write_str("bitcoin_without_primitives"),
            Category::SignatureHashModes => f.write_str("signature_hash_modes"),
            Category::TimeLocks => f.write_str("time_locks"),
            Category::Issuance => f.write_str("issuance"),
            Category::Transaction => f.write_str("transaction"),
        }
    }
}

impl Category {
    pub const ALL: [Self; 10] = [
        Self::MultiBitLogic,
        Self::Arithmetic,
        Self::HashFunctions,
        Self::EllipticCurveFunctions,
        Self::DigitalSignatures,
        Self::BitcoinWithoutPrimitives,
        Self::SignatureHashModes,
        Self::TimeLocks,
        Self::Issuance,
        Self::Transaction,
    ];

    pub const fn documentation(self) -> &'static str {
        match self {
            Self::MultiBitLogic => {
                r#"//! # Multi-bit logic
//!
//! This module defines jets that operate on strings of bits."#
            }
            Self::Arithmetic => {
                r#"//! # Arithmetic
//!
//! This module defines jets that compute arithmetic functions."#
            }
            Self::HashFunctions => {
                r#"//! # Hash functions
//!
//! This module defines jets for computing SHA-256 hashes.
//! Be aware that SHA-256 padding isn't provided and messages should be manually padded."#
            }
            Self::EllipticCurveFunctions => {
                r#"//! # Elliptic curve functions
//!
//! This module defines jets that replicate the functional behavior of (a specific version of) libsecp256k1's elliptic curve operations <https://github.com/bitcoin-core/secp256k1/tree/v0.3.0>.
//! The functions defined here return precisely the same field and point representatives that the corresponding libsecp256k1's functions do, with a few exceptions with the way the point at infinity is handled."#
            }
            Self::DigitalSignatures => {
                r#"//! # Digital signatures
//!
//! This module defines jets for verifying digital signatures."#
            }
            Self::BitcoinWithoutPrimitives => {
                r#"//! # Bitcoin (without primitives)
//!
//! This module defines jets for Bitcoin that work without the Bitcoin transaction environmnent.
//! These jets are not recommended for non-Bitcoin(-like) applications."#
            }
            Self::SignatureHashModes => {
                r#"//! # Elements signature hash modes
//!
//! This module defines jets for computing signature hashes of Elements transactions."#
            }
            Self::TimeLocks => {
                r#"//! # Time locks
//!
//! This module defines jets for checking time locks of Elements transactions."#
            }
            Self::Issuance => {
                r#"//! # Issuance
//!
//! This module defines jets for handling issuance of Elements assets or tokens."#
            }
            Self::Transaction => {
                r#"//! Transaction
//!
//! This module defines jets to introspect the contents of an Elements transaction."#
            }
        }
    }

    /// Check if a jet is contained in the category.
    #[cfg(test)]
    pub fn contains(&self, jet: &Elements) -> bool {
        match self {
            Self::MultiBitLogic => MULTI_BIT_LOGIC.contains(jet),
            Self::Arithmetic => ARITHMETIC.contains(jet),
            Self::HashFunctions => HASH_FUNCTIONS.contains(jet),
            Self::EllipticCurveFunctions => ELLIPTIC_CURVE_FUNCTIONS.contains(jet),
            Self::DigitalSignatures => DIGITAL_SIGNATURES.contains(jet),
            Self::BitcoinWithoutPrimitives => BITCOIN.contains(jet),
            Self::SignatureHashModes => SIGNATURE_HASH_MODES.contains(jet),
            Self::TimeLocks => TIME_LOCKS.contains(jet),
            Self::Issuance => ISSUANCE.contains(jet),
            Self::Transaction => TRANSACTION.contains(jet),
        }
    }

    /// Iterate over all jets in the category.
    pub fn iter(&self) -> impl Iterator<Item = &Elements> {
        match self {
            Self::MultiBitLogic => MULTI_BIT_LOGIC.iter(),
            Self::Arithmetic => ARITHMETIC.iter(),
            Self::HashFunctions => HASH_FUNCTIONS.iter(),
            Self::EllipticCurveFunctions => ELLIPTIC_CURVE_FUNCTIONS.iter(),
            Self::DigitalSignatures => DIGITAL_SIGNATURES.iter(),
            Self::BitcoinWithoutPrimitives => BITCOIN.iter(),
            Self::SignatureHashModes => SIGNATURE_HASH_MODES.iter(),
            Self::TimeLocks => TIME_LOCKS.iter(),
            Self::Issuance => ISSUANCE.iter(),
            Self::Transaction => TRANSACTION.iter(),
        }
    }
}

// Core
#[rustfmt::skip]
const MULTI_BIT_LOGIC: [Elements; 212] = [
    Elements::All8, Elements::All16, Elements::All32, Elements::All64, Elements::And1, Elements::And8, Elements::And16, Elements::And32, Elements::And64, Elements::Ch1, Elements::Ch8, Elements::Ch16, Elements::Ch32, Elements::Ch64, Elements::Complement1, Elements::Complement8, Elements::Complement16, Elements::Complement32, Elements::Complement64, Elements::Eq1, Elements::Eq8, Elements::Eq16, Elements::Eq32, Elements::Eq64, Elements::Eq256, Elements::FullLeftShift16_1, Elements::FullLeftShift16_2, Elements::FullLeftShift16_4, Elements::FullLeftShift16_8, Elements::FullLeftShift32_1, Elements::FullLeftShift32_2, Elements::FullLeftShift32_4, Elements::FullLeftShift32_8, Elements::FullLeftShift32_16, Elements::FullLeftShift64_1, Elements::FullLeftShift64_2, Elements::FullLeftShift64_4, Elements::FullLeftShift64_8, Elements::FullLeftShift64_16, Elements::FullLeftShift64_32, Elements::FullLeftShift8_1, Elements::FullLeftShift8_2, Elements::FullLeftShift8_4, Elements::FullRightShift16_1, Elements::FullRightShift16_2, Elements::FullRightShift16_4, Elements::FullRightShift16_8, Elements::FullRightShift32_1, Elements::FullRightShift32_2, Elements::FullRightShift32_4, Elements::FullRightShift32_8, Elements::FullRightShift32_16, Elements::FullRightShift64_1, Elements::FullRightShift64_2, Elements::FullRightShift64_4, Elements::FullRightShift64_8, Elements::FullRightShift64_16, Elements::FullRightShift64_32, Elements::FullRightShift8_1, Elements::FullRightShift8_2, Elements::FullRightShift8_4, Elements::High1, Elements::High8, Elements::High16, Elements::High32, Elements::High64, Elements::LeftExtend16_32, Elements::LeftExtend16_64, Elements::LeftExtend1_8, Elements::LeftExtend1_16, Elements::LeftExtend1_32, Elements::LeftExtend1_64, Elements::LeftExtend32_64, Elements::LeftExtend8_16, Elements::LeftExtend8_32, Elements::LeftExtend8_64, Elements::LeftPadHigh16_32, Elements::LeftPadHigh16_64, Elements::LeftPadHigh1_8, Elements::LeftPadHigh1_16, Elements::LeftPadHigh1_32, Elements::LeftPadHigh1_64, Elements::LeftPadHigh32_64, Elements::LeftPadHigh8_16, Elements::LeftPadHigh8_32, Elements::LeftPadHigh8_64, Elements::LeftPadLow16_32, Elements::LeftPadLow16_64, Elements::LeftPadLow1_8, Elements::LeftPadLow1_16, Elements::LeftPadLow1_32, Elements::LeftPadLow1_64, Elements::LeftPadLow32_64, Elements::LeftPadLow8_16, Elements::LeftPadLow8_32, Elements::LeftPadLow8_64, Elements::LeftRotate8, Elements::LeftRotate16, Elements::LeftRotate32, Elements::LeftRotate64, Elements::LeftShift8, Elements::LeftShift16, Elements::LeftShift32, Elements::LeftShift64, Elements::LeftShiftWith8, Elements::LeftShiftWith16, Elements::LeftShiftWith32, Elements::LeftShiftWith64, Elements::Leftmost16_1, Elements::Leftmost16_2, Elements::Leftmost16_4, Elements::Leftmost16_8, Elements::Leftmost32_1, Elements::Leftmost32_2, Elements::Leftmost32_4, Elements::Leftmost32_8, Elements::Leftmost32_16, Elements::Leftmost64_1, Elements::Leftmost64_2, Elements::Leftmost64_4, Elements::Leftmost64_8, Elements::Leftmost64_16, Elements::Leftmost64_32, Elements::Leftmost8_1, Elements::Leftmost8_2, Elements::Leftmost8_4, Elements::Low1, Elements::Low8, Elements::Low16, Elements::Low32, Elements::Low64, Elements::Maj1, Elements::Maj8, Elements::Maj16, Elements::Maj32, Elements::Maj64, Elements::Or1, Elements::Or8, Elements::Or16, Elements::Or32, Elements::Or64, Elements::RightExtend16_32, Elements::RightExtend16_64, Elements::RightExtend32_64, Elements::RightExtend8_16, Elements::RightExtend8_32, Elements::RightExtend8_64, Elements::RightPadHigh16_32, Elements::RightPadHigh16_64, Elements::RightPadHigh1_8, Elements::RightPadHigh1_16, Elements::RightPadHigh1_32, Elements::RightPadHigh1_64, Elements::RightPadHigh32_64, Elements::RightPadHigh8_16, Elements::RightPadHigh8_32, Elements::RightPadHigh8_64, Elements::RightPadLow16_32, Elements::RightPadLow16_64, Elements::RightPadLow1_8, Elements::RightPadLow1_16, Elements::RightPadLow1_32, Elements::RightPadLow1_64, Elements::RightPadLow32_64, Elements::RightPadLow8_16, Elements::RightPadLow8_32, Elements::RightPadLow8_64, Elements::RightRotate8, Elements::RightRotate16, Elements::RightRotate32, Elements::RightRotate64, Elements::RightShift8, Elements::RightShift16, Elements::RightShift32, Elements::RightShift64, Elements::RightShiftWith8, Elements::RightShiftWith16, Elements::RightShiftWith32, Elements::RightShiftWith64, Elements::Rightmost16_1, Elements::Rightmost16_2, Elements::Rightmost16_4, Elements::Rightmost16_8, Elements::Rightmost32_1, Elements::Rightmost32_2, Elements::Rightmost32_4, Elements::Rightmost32_8, Elements::Rightmost32_16, Elements::Rightmost64_1, Elements::Rightmost64_2, Elements::Rightmost64_4, Elements::Rightmost64_8, Elements::Rightmost64_16, Elements::Rightmost64_32, Elements::Rightmost8_1, Elements::Rightmost8_2, Elements::Rightmost8_4, Elements::Some1, Elements::Some8, Elements::Some16, Elements::Some32, Elements::Some64, Elements::Xor1, Elements::Xor8, Elements::Xor16, Elements::Xor32, Elements::Xor64, Elements::XorXor1, Elements::XorXor8, Elements::XorXor16, Elements::XorXor32, Elements::XorXor64
];
#[rustfmt::skip]
const ARITHMETIC: [Elements; 93] = [
    Elements::Add8, Elements::Add16, Elements::Add32, Elements::Add64, Elements::Decrement8, Elements::Decrement16, Elements::Decrement32, Elements::Decrement64, Elements::DivMod8, Elements::DivMod16, Elements::DivMod32, Elements::DivMod64, Elements::DivMod128_64, Elements::Divide8, Elements::Divide16, Elements::Divide32, Elements::Divide64, Elements::Divides8, Elements::Divides16, Elements::Divides32, Elements::Divides64, Elements::FullAdd8, Elements::FullAdd16, Elements::FullAdd32, Elements::FullAdd64, Elements::FullDecrement8, Elements::FullDecrement16, Elements::FullDecrement32, Elements::FullDecrement64, Elements::FullIncrement8, Elements::FullIncrement16, Elements::FullIncrement32, Elements::FullIncrement64, Elements::FullMultiply8, Elements::FullMultiply16, Elements::FullMultiply32, Elements::FullMultiply64, Elements::FullSubtract8, Elements::FullSubtract16, Elements::FullSubtract32, Elements::FullSubtract64, Elements::Increment8, Elements::Increment16, Elements::Increment32, Elements::Increment64, Elements::IsOne8, Elements::IsOne16, Elements::IsOne32, Elements::IsOne64, Elements::IsZero8, Elements::IsZero16, Elements::IsZero32, Elements::IsZero64, Elements::Le8, Elements::Le16, Elements::Le32, Elements::Le64, Elements::Lt8, Elements::Lt16, Elements::Lt32, Elements::Lt64, Elements::Max8, Elements::Max16, Elements::Max32, Elements::Max64, Elements::Median8, Elements::Median16, Elements::Median32, Elements::Median64, Elements::Min8, Elements::Min16, Elements::Min32, Elements::Min64, Elements::Modulo8, Elements::Modulo16, Elements::Modulo32, Elements::Modulo64, Elements::Multiply8, Elements::Multiply16, Elements::Multiply32, Elements::Multiply64, Elements::Negate8, Elements::Negate16, Elements::Negate32, Elements::Negate64, Elements::One8, Elements::One16, Elements::One32, Elements::One64, Elements::Subtract8, Elements::Subtract16, Elements::Subtract32, Elements::Subtract64
];
#[rustfmt::skip]
const HASH_FUNCTIONS: [Elements; 15] = [
    Elements::Sha256Block, Elements::Sha256Ctx8Add1, Elements::Sha256Ctx8Add2, Elements::Sha256Ctx8Add4, Elements::Sha256Ctx8Add8, Elements::Sha256Ctx8Add16, Elements::Sha256Ctx8Add32, Elements::Sha256Ctx8Add64, Elements::Sha256Ctx8Add128, Elements::Sha256Ctx8Add256, Elements::Sha256Ctx8Add512, Elements::Sha256Ctx8AddBuffer511, Elements::Sha256Ctx8Finalize, Elements::Sha256Ctx8Init, Elements::Sha256Iv
];
#[rustfmt::skip]
const ELLIPTIC_CURVE_FUNCTIONS: [Elements; 42] = [
    Elements::Decompress, Elements::FeAdd, Elements::FeInvert, Elements::FeIsOdd, Elements::FeIsZero, Elements::FeMultiply, Elements::FeMultiplyBeta, Elements::FeNegate, Elements::FeNormalize, Elements::FeSquare, Elements::FeSquareRoot, Elements::GeIsOnCurve, Elements::GeNegate, Elements::GejAdd, Elements::GejDouble, Elements::GejEquiv, Elements::GejGeAdd, Elements::GejGeAddEx, Elements::GejGeEquiv, Elements::GejInfinity, Elements::GejIsInfinity, Elements::GejIsOnCurve, Elements::GejNegate, Elements::GejNormalize, Elements::GejRescale, Elements::GejXEquiv, Elements::GejYIsOdd, Elements::Generate, Elements::HashToCurve, Elements::LinearCombination1, Elements::LinearVerify1, Elements::PointVerify1, Elements::ScalarAdd, Elements::ScalarInvert, Elements::ScalarIsZero, Elements::ScalarMultiply, Elements::ScalarMultiplyLambda, Elements::ScalarNegate, Elements::ScalarNormalize, Elements::ScalarSquare, Elements::Scale, Elements::Swu
];
#[rustfmt::skip]
const DIGITAL_SIGNATURES: [Elements; 1] = [
    Elements::Bip0340Verify
];
#[rustfmt::skip]
const BITCOIN: [Elements; 3] = [
    Elements::ParseLock, Elements::ParseSequence, Elements::TapdataInit,
];
// Elements
#[rustfmt::skip]
const SIGNATURE_HASH_MODES: [Elements; 35] = [
    Elements::AnnexHash, Elements::AssetAmountHash, Elements::BuildTapbranch, Elements::BuildTapleafSimplicity, Elements::BuildTaptweak, Elements::InputAmountsHash, Elements::InputAnnexesHash, Elements::InputHash, Elements::InputOutpointsHash, Elements::InputScriptSigsHash, Elements::InputScriptsHash, Elements::InputSequencesHash, Elements::InputUtxoHash, Elements::InputUtxosHash, Elements::InputsHash, Elements::IssuanceAssetAmountsHash, Elements::IssuanceBlindingEntropyHash, Elements::IssuanceHash, Elements::IssuanceRangeProofsHash, Elements::IssuanceTokenAmountsHash, Elements::IssuancesHash, Elements::NonceHash, Elements::OutpointHash, Elements::OutputAmountsHash, Elements::OutputHash, Elements::OutputNoncesHash, Elements::OutputRangeProofsHash, Elements::OutputScriptsHash, Elements::OutputSurjectionProofsHash, Elements::OutputsHash, Elements::SigAllHash, Elements::TapEnvHash, Elements::TapleafHash, Elements::TappathHash, Elements::TxHash
];
#[rustfmt::skip]
const TIME_LOCKS: [Elements; 9] = [
    Elements::CheckLockDistance, Elements::CheckLockDuration, Elements::CheckLockHeight, Elements::CheckLockTime, Elements::TxIsFinal, Elements::TxLockDistance, Elements::TxLockDuration, Elements::TxLockHeight, Elements::TxLockTime
];
#[rustfmt::skip]
const ISSUANCE: [Elements; 9] = [
    Elements::CalculateAsset, Elements::CalculateConfidentialToken, Elements::CalculateExplicitToken, Elements::CalculateIssuanceEntropy, Elements::Issuance, Elements::IssuanceAsset, Elements::IssuanceEntropy, Elements::IssuanceToken, Elements::LbtcAsset
];
#[rustfmt::skip]
const TRANSACTION: [Elements; 50] = [
    Elements::CurrentAmount, Elements::CurrentAnnexHash, Elements::CurrentAsset, Elements::CurrentIndex, Elements::CurrentIssuanceAssetAmount, Elements::CurrentIssuanceAssetProof, Elements::CurrentIssuanceTokenAmount, Elements::CurrentIssuanceTokenProof, Elements::CurrentNewIssuanceContract, Elements::CurrentPegin, Elements::CurrentPrevOutpoint, Elements::CurrentReissuanceBlinding, Elements::CurrentReissuanceEntropy, Elements::CurrentScriptHash, Elements::CurrentScriptSigHash, Elements::CurrentSequence, Elements::GenesisBlockHash, Elements::InputAmount, Elements::InputAnnexHash, Elements::InputAsset, Elements::InputPegin, Elements::InputPrevOutpoint, Elements::InputScriptHash, Elements::InputScriptSigHash, Elements::InputSequence, Elements::InternalKey, Elements::IssuanceAssetAmount, Elements::IssuanceAssetProof, Elements::IssuanceTokenAmount, Elements::IssuanceTokenProof, Elements::LockTime, Elements::NewIssuanceContract, Elements::NumInputs, Elements::NumOutputs, Elements::OutputAmount, Elements::OutputAsset, Elements::OutputIsFee, Elements::OutputNonce, Elements::OutputNullDatum, Elements::OutputRangeProof, Elements::OutputScriptHash, Elements::OutputSurjectionProof, Elements::ReissuanceBlinding, Elements::ReissuanceEntropy, Elements::ScriptCMR, Elements::TapleafVersion, Elements::Tappath, Elements::TotalFee, Elements::TransactionId, Elements::Version
];

#[cfg(test)]
mod tests {
    use super::*;

    #[rustfmt::skip]
    const DISABLED: [Elements; 2] = [
        Elements::CheckSigVerify, Elements::Verify
    ];

    #[test]
    fn correct_categorization() {
        for jet in Elements::ALL {
            match Category::ALL.iter().find(|c| c.contains(&jet)) {
                Some(category) => {
                    if let Some(other) = Category::ALL
                        .into_iter()
                        .filter(|other| other != category)
                        .find(|other| other.contains(&jet))
                    {
                        panic!("{jet} is assigned conflicting categories {category} and {other}");
                    }
                }
                None => {
                    assert!(DISABLED.contains(&jet), "{jet} is not categorized");
                }
            }
        }
    }
}
