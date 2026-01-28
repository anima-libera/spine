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
pub(crate) enum Raw8 {
	Signed(i8),
	Unsigned(u8),
}
#[derive(Clone, Copy)]
pub(crate) enum Raw32 {
	Signed(i32),
	Unsigned(u32),
}
#[derive(Clone, Copy)]
pub(crate) enum Raw64 {
	Signed(i64),
	Unsigned(u64),
}

macro_rules! impl_raw_is_signed {
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
impl_raw_is_signed!(Raw8);
impl_raw_is_signed!(Raw32);
impl_raw_is_signed!(Raw64);

macro_rules! impl_raw_is_zero {
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
impl_raw_is_zero!(Raw8);
impl_raw_is_zero!(Raw32);
impl_raw_is_zero!(Raw64);

macro_rules! impl_raw_to_bytes {
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
impl_raw_to_bytes!(Raw64, to_8_bytes, i64, u64, 8);
impl_raw_to_bytes!(Raw32, to_8_bytes, i64, u64, 8);
impl_raw_to_bytes!(Raw32, to_4_bytes, i32, u32, 4);
impl_raw_to_bytes!(Raw8, to_8_bytes, i64, u64, 8);
impl_raw_to_bytes!(Raw8, to_4_bytes, i32, u32, 4);
impl_raw_to_bytes!(Raw8, to_1_bytes, i8, u8, 1);

impl Raw64 {
	pub(crate) fn to_u64(self) -> u64 {
		match self {
			Raw64::Signed(value) => value.cast_unsigned(),
			Raw64::Unsigned(value) => value,
		}
	}
}
impl Raw32 {
	pub(crate) fn to_u32(self) -> u32 {
		match self {
			Raw32::Signed(value) => value.cast_unsigned(),
			Raw32::Unsigned(value) => value,
		}
	}
}
impl Raw8 {
	pub(crate) fn to_u8(self) -> u8 {
		match self {
			Raw8::Signed(value) => value.cast_unsigned(),
			Raw8::Unsigned(value) => value,
		}
	}
}

pub(crate) enum Imm8 {
	Raw(Raw8),
}

impl Imm8 {
	pub(crate) fn to_raw_8(&self, _layout: &Layout) -> Raw8 {
		match self {
			Imm8::Raw(raw) => *raw,
		}
	}

	pub(crate) fn is_signed(&self) -> bool {
		matches!(self, Imm8::Raw(Raw8::Signed(_)))
	}

	pub(crate) fn is_raw_zero(&self) -> bool {
		matches!(self, Imm8::Raw(raw8) if raw8.is_zero())
	}
}

pub(crate) enum Imm32 {
	DataAddr { offset_in_data_segment: u32 },
	Raw(Raw32),
}

impl Imm32 {
	pub(crate) fn to_raw_32(&self, layout: &Layout) -> Raw32 {
		match self {
			Imm32::DataAddr { offset_in_data_segment } => {
				Raw32::Unsigned(layout.data_segment_address as u32 + offset_in_data_segment)
			},
			Imm32::Raw(raw) => *raw,
		}
	}

	pub(crate) fn is_signed(&self) -> bool {
		matches!(self, Imm32::Raw(Raw32::Signed(_)))
	}

	pub(crate) fn is_raw_zero(&self) -> bool {
		matches!(self, Imm32::Raw(raw32) if raw32.is_zero())
	}
}

pub(crate) enum Imm64 {
	DataAddr { offset_in_data_segment: u64 },
	Raw(Raw64),
}

impl Imm64 {
	pub(crate) fn to_raw_64(&self, layout: &Layout) -> Raw64 {
		match self {
			Imm64::DataAddr { offset_in_data_segment } => {
				Raw64::Unsigned(layout.data_segment_address as u64 + offset_in_data_segment)
			},
			Imm64::Raw(raw) => *raw,
		}
	}

	pub(crate) fn is_signed(&self) -> bool {
		matches!(self, Imm64::Raw(Raw64::Signed(_)))
	}

	pub(crate) fn is_raw_zero(&self) -> bool {
		matches!(self, Imm64::Raw(raw64) if raw64.is_zero())
	}
}

pub(crate) enum Imm {
	Imm8(Imm8),
	Imm32(Imm32),
	Imm64(Imm64),
}

impl Imm {
	pub(crate) fn signed_raw(value: i64) -> Imm {
		if let Ok(value) = value.try_into() {
			Imm::Imm8(Imm8::Raw(Raw8::Signed(value)))
		} else if let Ok(value) = value.try_into() {
			Imm::Imm32(Imm32::Raw(Raw32::Signed(value)))
		} else {
			Imm::Imm64(Imm64::Raw(Raw64::Signed(value)))
		}
	}

	pub(crate) fn unsigned_raw(value: u64) -> Imm {
		if let Ok(value) = value.try_into() {
			Imm::Imm8(Imm8::Raw(Raw8::Unsigned(value)))
		} else if let Ok(value) = value.try_into() {
			Imm::Imm32(Imm32::Raw(Raw32::Unsigned(value)))
		} else {
			Imm::Imm64(Imm64::Raw(Raw64::Unsigned(value)))
		}
	}

	pub(crate) fn whatever_raw(value: i64) -> Imm {
		if value < 0 {
			Self::signed_raw(value)
		} else {
			Self::unsigned_raw(value as u64)
		}
	}

	pub(crate) fn is_signed(&self) -> bool {
		match self {
			Imm::Imm8(imm8) => imm8.is_signed(),
			Imm::Imm32(imm32) => imm32.is_signed(),
			Imm::Imm64(imm64) => imm64.is_signed(),
		}
	}

	pub(crate) fn is_raw_zero(&self) -> bool {
		match self {
			Imm::Imm8(imm8) => imm8.is_raw_zero(),
			Imm::Imm32(imm32) => imm32.is_raw_zero(),
			Imm::Imm64(imm64) => imm64.is_raw_zero(),
		}
	}

	pub(crate) fn to_8_bytes(&self, layout: &Layout) -> [u8; 8] {
		match self {
			Imm::Imm8(imm8) => imm8.to_raw_8(layout).to_8_bytes(),
			Imm::Imm32(imm32) => imm32.to_raw_32(layout).to_8_bytes(),
			Imm::Imm64(imm64) => imm64.to_raw_64(layout).to_8_bytes(),
		}
	}
}
