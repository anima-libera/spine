// Immediate values `Imm8`, `Imm32` and `Imm64` can sometimes represent something (like a memory
// address of something in the data segment for example) that isn't just a raw number.
// Immediate values can also just be a raw number (either signed or unsigned btw).
// We make the difference here, with `Raw8`, `Raw32` and `Raw64` being different types than
// immediate value types, and immediate value types being convertible to raw values given
// some layout information available at the time assembly code is not being generated anymore
// and is ready to be converted to machine code, at the end.
// Unless there is a good reason, assembly instruction variants should hold immediate values
// with the `ImmN` types instead of the `RawN` types or the `uN`/`iN` types.

use crate::elf::Layout;

#[derive(Clone, Copy)]
pub(crate) enum Value8 {
	Signed(i8),
	Unsigned(u8),
}
#[derive(Clone, Copy)]
pub(crate) enum Value32 {
	Signed(i32),
	Unsigned(u32),
}
#[derive(Clone, Copy)]
pub(crate) enum Value64 {
	Signed(i64),
	Unsigned(u64),
}

macro_rules! impl_value_is_signed {
	($raw_n:ty) => {
		impl $raw_n {
			pub(crate) fn is_signed(self) -> bool {
				match self {
					Self::Signed(_) => true,
					Self::Unsigned(_) => false,
				}
			}
		}
	};
}
impl_value_is_signed!(Value8);
impl_value_is_signed!(Value32);
impl_value_is_signed!(Value64);

macro_rules! impl_value_is_zero {
	($raw_n:ty) => {
		impl $raw_n {
			pub(crate) fn is_zero(self) -> bool {
				match self {
					Self::Signed(value) => value == 0,
					Self::Unsigned(value) => value == 0,
				}
			}
		}
	};
}
impl_value_is_zero!(Value8);
impl_value_is_zero!(Value32);
impl_value_is_zero!(Value64);

macro_rules! impl_value_to_bytes {
	($raw_n:ty, $fn_name:ident, $as_signed:ty, $as_unsigned:ty, $size:literal) => {
		impl $raw_n {
			pub(crate) fn $fn_name(self) -> [u8; $size] {
				match self {
					Self::Signed(value) => (value as $as_signed).to_le_bytes(),
					Self::Unsigned(value) => (value as $as_unsigned).to_le_bytes(),
				}
			}
		}
	};
}
impl_value_to_bytes!(Value64, to_8_bytes, i64, u64, 8);
impl_value_to_bytes!(Value32, to_8_bytes, i64, u64, 8);
impl_value_to_bytes!(Value32, to_4_bytes, i32, u32, 4);
impl_value_to_bytes!(Value8, to_8_bytes, i64, u64, 8);
impl_value_to_bytes!(Value8, to_4_bytes, i32, u32, 4);
impl_value_to_bytes!(Value8, to_1_bytes, i8, u8, 1);

impl Value64 {
	pub(crate) fn to_u64(self) -> u64 {
		match self {
			Value64::Signed(value) => value.cast_unsigned(),
			Value64::Unsigned(value) => value,
		}
	}
}
impl Value32 {
	pub(crate) fn to_u32(self) -> u32 {
		match self {
			Value32::Signed(value) => value.cast_unsigned(),
			Value32::Unsigned(value) => value,
		}
	}
}
impl Value8 {
	pub(crate) fn to_u8(self) -> u8 {
		match self {
			Value8::Signed(value) => value.cast_unsigned(),
			Value8::Unsigned(value) => value,
		}
	}
}

pub(crate) enum ImmRich8 {
	Value(Value8),
}

impl ImmRich8 {
	pub(crate) fn to_value_8(&self, _layout: &Layout) -> Value8 {
		match self {
			ImmRich8::Value(value) => *value,
		}
	}

	pub(crate) fn is_signed(&self) -> bool {
		matches!(self, ImmRich8::Value(Value8::Signed(_)))
	}

	pub(crate) fn is_value_zero(&self) -> bool {
		matches!(self, ImmRich8::Value(value8) if value8.is_zero())
	}
}

pub(crate) enum ImmRich32 {
	DataAddr { offset_in_data_segment: u32 },
	Value(Value32),
}

impl ImmRich32 {
	pub(crate) fn to_value_32(&self, layout: &Layout) -> Value32 {
		match self {
			ImmRich32::DataAddr { offset_in_data_segment } => {
				Value32::Unsigned(layout.data_segment_address as u32 + offset_in_data_segment)
			},
			ImmRich32::Value(value) => *value,
		}
	}

	pub(crate) fn is_signed(&self) -> bool {
		matches!(self, ImmRich32::Value(Value32::Signed(_)))
	}

	pub(crate) fn is_value_zero(&self) -> bool {
		matches!(self, ImmRich32::Value(value32) if value32.is_zero())
	}
}

pub(crate) enum ImmRich64 {
	DataAddr { offset_in_data_segment: u64 },
	Value(Value64),
}

impl ImmRich64 {
	pub(crate) fn to_value_64(&self, layout: &Layout) -> Value64 {
		match self {
			ImmRich64::DataAddr { offset_in_data_segment } => {
				Value64::Unsigned(layout.data_segment_address as u64 + offset_in_data_segment)
			},
			ImmRich64::Value(value) => *value,
		}
	}

	pub(crate) fn is_signed(&self) -> bool {
		matches!(self, ImmRich64::Value(Value64::Signed(_)))
	}

	pub(crate) fn is_value_zero(&self) -> bool {
		matches!(self, ImmRich64::Value(value64) if value64.is_zero())
	}
}

/// What would become an immediate value, but with more info such as sign (signed/unsigned),
/// or can be an address to be determined later, etc.
pub(crate) enum ImmRich {
	Imm8(ImmRich8),
	Imm32(ImmRich32),
	Imm64(ImmRich64),
}

impl ImmRich {
	pub(crate) fn signed_value(value: i64) -> ImmRich {
		if let Ok(value) = value.try_into() {
			ImmRich::Imm8(ImmRich8::Value(Value8::Signed(value)))
		} else if let Ok(value) = value.try_into() {
			ImmRich::Imm32(ImmRich32::Value(Value32::Signed(value)))
		} else {
			ImmRich::Imm64(ImmRich64::Value(Value64::Signed(value)))
		}
	}

	pub(crate) fn unsigned_value(value: u64) -> ImmRich {
		if let Ok(value) = value.try_into() {
			ImmRich::Imm8(ImmRich8::Value(Value8::Unsigned(value)))
		} else if let Ok(value) = value.try_into() {
			ImmRich::Imm32(ImmRich32::Value(Value32::Unsigned(value)))
		} else {
			ImmRich::Imm64(ImmRich64::Value(Value64::Unsigned(value)))
		}
	}

	pub(crate) fn whatever_value(value: i64) -> ImmRich {
		if value < 0 {
			Self::signed_value(value)
		} else {
			Self::unsigned_value(value as u64)
		}
	}

	pub(crate) fn is_signed(&self) -> bool {
		match self {
			ImmRich::Imm8(imm8) => imm8.is_signed(),
			ImmRich::Imm32(imm32) => imm32.is_signed(),
			ImmRich::Imm64(imm64) => imm64.is_signed(),
		}
	}

	pub(crate) fn is_value_zero(&self) -> bool {
		match self {
			ImmRich::Imm8(imm8) => imm8.is_value_zero(),
			ImmRich::Imm32(imm32) => imm32.is_value_zero(),
			ImmRich::Imm64(imm64) => imm64.is_value_zero(),
		}
	}

	pub(crate) fn to_8_bytes(&self, layout: &Layout) -> [u8; 8] {
		match self {
			ImmRich::Imm8(imm8) => imm8.to_value_8(layout).to_8_bytes(),
			ImmRich::Imm32(imm32) => imm32.to_value_32(layout).to_8_bytes(),
			ImmRich::Imm64(imm64) => imm64.to_value_64(layout).to_8_bytes(),
		}
	}
}
