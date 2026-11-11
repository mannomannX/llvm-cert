use crate::error::BridgeError;

/// Scalar floating-point types in LLVM 23.1.5 IR.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FpScalarType {
    Half,
    BFloat,
    Float,
    Double,
    Fp128,
    X86Fp80,
    PpcFp128,
}

impl FpScalarType {
    pub(crate) fn from_keyword(tok: &str) -> Option<Self> {
        match tok {
            "half" => Some(Self::Half),
            "bfloat" => Some(Self::BFloat),
            "float" => Some(Self::Float),
            "double" => Some(Self::Double),
            "fp128" => Some(Self::Fp128),
            "x86_fp80" => Some(Self::X86Fp80),
            "ppc_fp128" => Some(Self::PpcFp128),
            _ => None,
        }
    }
}

/// Bit-exact IEEE-754 widening from binary32 (`u32` bits) to binary64 (`u64` bits).
///
/// Matches both LLVM's `LLLexer::Lex0x` (`APFloat::IEEEdouble` -> `IEEEsingle`) and
/// Vellvm's `Floats.of_single` / `VellvmFloats.hexadecimal_uint_to_float32` without
/// relying on host CPU floating-point instructions (preserving signaling NaN bits and payloads).
#[must_use]
pub fn f32_bits_to_f64_bits(bits32: u32) -> u64 {
    let sign64 = u64::from(bits32 >> 31) << 63;
    let exp32 = (bits32 >> 23) & 0xFF;
    let frac32 = bits32 & 0x007F_FFFF;

    if exp32 == 0 && frac32 == 0 {
        sign64
    } else if exp32 == 0xFF {
        sign64 | (0x7FF_u64 << 52) | (u64::from(frac32) << 29)
    } else if exp32 == 0 {
        // 32-bit subnormal: normalize leading 1 into bit 23 and adjust binary64 exponent.
        let shift = frac32.leading_zeros().saturating_sub(8);
        let norm_frac = (frac32 << shift) & 0x007F_FFFF;
        let exp64 = 897_u64.saturating_sub(u64::from(shift));
        sign64 | (exp64 << 52) | (u64::from(norm_frac) << 29)
    } else {
        let exp64 = u64::from(exp32) + 896;
        sign64 | (exp64 << 52) | (u64::from(frac32) << 29)
    }
}

fn convert_f0x_token(
    full_token: &str,
    hex_digits: &str,
    active_ty: Option<FpScalarType>,
) -> Result<String, BridgeError> {
    match hex_digits.len() {
        4 => {
            let val = u16::from_str_radix(hex_digits, 16).map_err(|_| {
                BridgeError::InvalidFloatLiteral {
                    token: full_token.to_owned(),
                    reason: "invalid 16-bit hex digits",
                }
            })?;
            let prefix = match active_ty {
                Some(FpScalarType::BFloat) => "0xR",
                _ => "0xH",
            };
            Ok(format!("{prefix}{val:04X}"))
        }
        8 => {
            let bits32 = u32::from_str_radix(hex_digits, 16).map_err(|_| {
                BridgeError::InvalidFloatLiteral {
                    token: full_token.to_owned(),
                    reason: "invalid 32-bit hex digits",
                }
            })?;
            let bits64 = f32_bits_to_f64_bits(bits32);
            Ok(format!("0x{bits64:016X}"))
        }
        16 => {
            let bits64 = u64::from_str_radix(hex_digits, 16).map_err(|_| {
                BridgeError::InvalidFloatLiteral {
                    token: full_token.to_owned(),
                    reason: "invalid 64-bit hex digits",
                }
            })?;
            Ok(format!("0x{bits64:016X}"))
        }
        20 => {
            if !hex_digits.bytes().all(|b| b.is_ascii_hexdigit()) {
                return Err(BridgeError::InvalidFloatLiteral {
                    token: full_token.to_owned(),
                    reason: "invalid 80-bit hex digits",
                });
            }
            Ok(format!("0xK{}", hex_digits.to_ascii_uppercase()))
        }
        32 => {
            let bits128 = u128::from_str_radix(hex_digits, 16).map_err(|_| {
                BridgeError::InvalidFloatLiteral {
                    token: full_token.to_owned(),
                    reason: "invalid 128-bit hex digits",
                }
            })?;
            let prefix = match active_ty {
                Some(FpScalarType::PpcFp128) => "0xM",
                _ => "0xL",
            };
            Ok(format!("{prefix}{bits128:032X}"))
        }
        _ => Err(BridgeError::InvalidFloatLiteral {
            token: full_token.to_owned(),
            reason: "unsupported f0x hex bitwidth (expected 4, 8, 16, 20, or 32 hex digits)",
        }),
    }
}

fn convert_special_fp_token(
    full_token: &str,
    is_negative: bool,
    kind: SpecialFpKind<'_>,
    active_ty: Option<FpScalarType>,
) -> Result<String, BridgeError> {
    let ty = active_ty.unwrap_or(FpScalarType::Double);
    match ty {
        FpScalarType::Float => {
            let sign32 = if is_negative { 0x8000_0000_u32 } else { 0 };
            let bits32 = match kind {
                SpecialFpKind::Inf => sign32 | 0x7F80_0000,
                SpecialFpKind::QNaN => sign32 | 0x7FC0_0000,
                SpecialFpKind::NaNPayload { signaling, hex } => {
                    let payload = parse_nan_payload_u128(full_token, hex, 22, signaling)?;
                    let payload32 =
                        u32::try_from(payload).map_err(|_| BridgeError::InvalidFloatLiteral {
                            token: full_token.to_owned(),
                            reason: "NaN payload overflows 32-bit float",
                        })?;
                    let quiet_bit = if signaling { 0 } else { 0x0040_0000 };
                    sign32 | 0x7F80_0000 | quiet_bit | payload32
                }
            };
            Ok(format!("0x{:016X}", f32_bits_to_f64_bits(bits32)))
        }
        FpScalarType::Double => {
            let sign64 = if is_negative { 1_u64 << 63 } else { 0 };
            let bits64 = match kind {
                SpecialFpKind::Inf => sign64 | (0x7FF_u64 << 52),
                SpecialFpKind::QNaN => sign64 | 0x7FF8_0000_0000_0000,
                SpecialFpKind::NaNPayload { signaling, hex } => {
                    let payload = parse_nan_payload_u128(full_token, hex, 51, signaling)?;
                    let payload64 =
                        u64::try_from(payload).map_err(|_| BridgeError::InvalidFloatLiteral {
                            token: full_token.to_owned(),
                            reason: "NaN payload overflows 64-bit double",
                        })?;
                    let quiet_bit = if signaling { 0 } else { 1_u64 << 51 };
                    sign64 | (0x7FF_u64 << 52) | quiet_bit | payload64
                }
            };
            Ok(format!("0x{bits64:016X}"))
        }
        FpScalarType::Half => {
            let sign16 = if is_negative { 0x8000_u16 } else { 0 };
            let bits16 = match kind {
                SpecialFpKind::Inf => sign16 | 0x7C00,
                SpecialFpKind::QNaN => sign16 | 0x7E00,
                SpecialFpKind::NaNPayload { signaling, hex } => {
                    let payload = parse_nan_payload_u128(full_token, hex, 9, signaling)?;
                    let payload16 =
                        u16::try_from(payload).map_err(|_| BridgeError::InvalidFloatLiteral {
                            token: full_token.to_owned(),
                            reason: "NaN payload overflows 16-bit half",
                        })?;
                    let quiet_bit = if signaling { 0 } else { 0x0200 };
                    sign16 | 0x7C00 | quiet_bit | payload16
                }
            };
            Ok(format!("0xH{bits16:04X}"))
        }
        FpScalarType::BFloat => {
            let sign16 = if is_negative { 0x8000_u16 } else { 0 };
            let bits16 = match kind {
                SpecialFpKind::Inf => sign16 | 0x7F80,
                SpecialFpKind::QNaN => sign16 | 0x7FC0,
                SpecialFpKind::NaNPayload { signaling, hex } => {
                    let payload = parse_nan_payload_u128(full_token, hex, 6, signaling)?;
                    let payload16 =
                        u16::try_from(payload).map_err(|_| BridgeError::InvalidFloatLiteral {
                            token: full_token.to_owned(),
                            reason: "NaN payload overflows 16-bit bfloat",
                        })?;
                    let quiet_bit = if signaling { 0 } else { 0x0040 };
                    sign16 | 0x7F80 | quiet_bit | payload16
                }
            };
            Ok(format!("0xR{bits16:04X}"))
        }
        FpScalarType::Fp128 | FpScalarType::PpcFp128 => {
            let sign128 = if is_negative { 1_u128 << 127 } else { 0 };
            let bits128 = match kind {
                SpecialFpKind::Inf => sign128 | (0x7FFF_u128 << 112),
                SpecialFpKind::QNaN => sign128 | (0x0007_FFF8_u128 << 108),
                SpecialFpKind::NaNPayload { signaling, hex } => {
                    let payload = parse_nan_payload_u128(full_token, hex, 111, signaling)?;
                    let quiet_bit = if signaling { 0 } else { 1_u128 << 111 };
                    sign128 | (0x7FFF_u128 << 112) | quiet_bit | payload
                }
            };
            let prefix = if ty == FpScalarType::PpcFp128 {
                "0xM"
            } else {
                "0xL"
            };
            Ok(format!("{prefix}{bits128:032X}"))
        }
        FpScalarType::X86Fp80 => Err(BridgeError::InvalidFloatLiteral {
            token: full_token.to_owned(),
            reason: "symbolic inf/nan on x86_fp80 is unsupported on AArch64/RISCV targets",
        }),
    }
}

enum SpecialFpKind<'a> {
    Inf,
    QNaN,
    NaNPayload { signaling: bool, hex: &'a str },
}

fn parse_nan_payload_u128(
    full_token: &str,
    hex_with_prefix: &str,
    payload_bits: u32,
    signaling: bool,
) -> Result<u128, BridgeError> {
    let hex = hex_with_prefix
        .strip_prefix("0x")
        .or_else(|| hex_with_prefix.strip_prefix("0X"))
        .ok_or_else(|| BridgeError::InvalidFloatLiteral {
            token: full_token.to_owned(),
            reason: "NaN payload must begin with 0x",
        })?;
    let val = u128::from_str_radix(hex, 16).map_err(|_| BridgeError::InvalidFloatLiteral {
        token: full_token.to_owned(),
        reason: "invalid hexadecimal NaN payload",
    })?;
    let limit = 1_u128 << payload_bits;
    if val >= limit {
        return Err(BridgeError::InvalidFloatLiteral {
            token: full_token.to_owned(),
            reason: "NaN payload exceeds mantissa payload bitwidth",
        });
    }
    if signaling && val == 0 {
        return Err(BridgeError::InvalidFloatLiteral {
            token: full_token.to_owned(),
            reason: "signaling NaN payload must be non-zero",
        });
    }
    Ok(val)
}

fn is_llvm_ident_prefix(b: u8) -> bool {
    matches!(b, b'%' | b'@' | b'$' | b'!' | b'#')
}

fn is_word_byte(b: u8) -> bool {
    b.is_ascii_alphanumeric() || matches!(b, b'_' | b'.' | b'$' | b'-')
}

/// Normalizes LLVM 23.1.5 floating-point literals (`f0x<hex>`, `+-inf`, `+-qnan`, `+-s?nan(0x...)`)
/// into canonical `0x<hex>` IEEE constants accepted identically by Vellvm 3.0 and LLVM 23,
/// and strips inline C-style `/* ... */` block comments (`/* immarg */`).
pub fn normalize_llvm23_fp_and_comments(ir: &str) -> Result<String, BridgeError> {
    let bytes = ir.as_bytes();
    let len = bytes.len();
    let mut out = String::with_capacity(len);
    let mut i = 0_usize;
    let mut active_fp: Option<FpScalarType> = None;

    while i < len {
        let Some(&b) = bytes.get(i) else {
            break;
        };

        // Preserve double-quoted strings verbatim (including `\"` / `\XX` escapes).
        if b == b'"' {
            let start = i;
            i += 1;
            while let Some(&ch) = bytes.get(i) {
                if ch == b'\\' {
                    i = (i + 2).min(len);
                    continue;
                }
                i += 1;
                if ch == b'"' {
                    break;
                }
            }
            if let Some(seg) = ir.get(start..i) {
                out.push_str(seg);
            }
            continue;
        }

        // Preserve `; ...` line comments verbatim.
        if b == b';' {
            let start = i;
            while let Some(&ch) = bytes.get(i) {
                i += 1;
                if ch == b'\n' {
                    active_fp = None;
                    break;
                }
            }
            if let Some(seg) = ir.get(start..i) {
                out.push_str(seg);
            }
            continue;
        }

        // Strip inline `/* ... */` block comments (e.g. `/* immarg */` in LLVM 23 intrinsics).
        if b == b'/' && bytes.get(i + 1) == Some(&b'*') {
            i += 2;
            let mut closed = false;
            while i + 1 < len {
                if bytes.get(i) == Some(&b'*') && bytes.get(i + 1) == Some(&b'/') {
                    i += 2;
                    closed = true;
                    break;
                }
                i += 1;
            }
            if !closed {
                return Err(BridgeError::UnterminatedBlockComment);
            }
            out.push(' ');
            continue;
        }

        if b == b'\n' {
            active_fp = None;
            out.push('\n');
            i += 1;
            continue;
        }

        // Consume `%local`, `@global`, `$comdat`, `!metadata`, `#attr` identifiers atomically
        // so names like `%f0x12345678` or `@inf` are never treated as FP literals.
        if is_llvm_ident_prefix(b) {
            let start = i;
            i += 1;
            if bytes.get(i) == Some(&b'"') {
                i += 1;
                while let Some(&ch) = bytes.get(i) {
                    if ch == b'\\' {
                        i = (i + 2).min(len);
                        continue;
                    }
                    i += 1;
                    if ch == b'"' {
                        break;
                    }
                }
            } else {
                while let Some(&ch) = bytes.get(i) {
                    if is_word_byte(ch) {
                        i += 1;
                    } else {
                        break;
                    }
                }
            }
            if let Some(seg) = ir.get(start..i) {
                out.push_str(seg);
            }
            continue;
        }

        // Check signed special FP tokens: `+inf`, `-inf`, `+qnan`, `-qnan`, `+-s?nan(0x...)`.
        if b == b'+' || b == b'-' {
            let is_neg = b == b'-';
            let rest = ir.get(i + 1..).unwrap_or("");
            if let Some((consumed, replacement)) =
                try_parse_signed_special_fp(ir, i, is_neg, rest, active_fp)?
            {
                out.push_str(&replacement);
                i += consumed;
                continue;
            }
        }

        // Scan bare word / keyword / `f0x...` token.
        if b.is_ascii_alphabetic() || b == b'_' {
            let start = i;
            while let Some(&ch) = bytes.get(i) {
                if is_word_byte(ch) {
                    i += 1;
                } else {
                    break;
                }
            }
            let word = ir.get(start..i).unwrap_or("");
            // Basic block labels (`entry:`, `f0x00000000:`) end with `:`.
            if bytes.get(i) == Some(&b':') {
                out.push_str(word);
                continue;
            }
            if let Some(fp_ty) = FpScalarType::from_keyword(word) {
                active_fp = Some(fp_ty);
                out.push_str(word);
                continue;
            }
            if let Some(hex) = word.strip_prefix("f0x")
                && !hex.is_empty()
                && hex.bytes().all(|c| c.is_ascii_hexdigit())
            {
                let converted = convert_f0x_token(word, hex, active_fp)?;
                out.push_str(&converted);
                continue;
            }
            out.push_str(word);
            continue;
        }

        // Copy single ASCII punctuation/digit/UTF-8 character safely.
        if let Some(ch) = ir.get(i..).and_then(|s| s.chars().next()) {
            out.push(ch);
            i += ch.len_utf8();
        } else {
            break;
        }
    }

    Ok(out)
}

fn try_parse_signed_special_fp(
    full_ir: &str,
    sign_idx: usize,
    is_neg: bool,
    after_sign: &str,
    active_fp: Option<FpScalarType>,
) -> Result<Option<(usize, String)>, BridgeError> {
    for (kw, is_qnan) in [("inf", false), ("qnan", true)] {
        if let Some(tail) = after_sign.strip_prefix(kw) {
            let next_byte = tail.as_bytes().first().copied();
            if !next_byte.is_some_and(is_word_byte) && next_byte != Some(b':') {
                let consumed = 1 + kw.len();
                let full_tok = full_ir.get(sign_idx..sign_idx + consumed).unwrap_or(kw);
                let kind = if is_qnan {
                    SpecialFpKind::QNaN
                } else {
                    SpecialFpKind::Inf
                };
                let converted = convert_special_fp_token(full_tok, is_neg, kind, active_fp)?;
                return Ok(Some((consumed, converted)));
            }
        }
    }

    for (prefix, signaling) in [("snan(", true), ("nan(", false)] {
        if let Some(after_open) = after_sign.strip_prefix(prefix)
            && let Some(close_pos) = after_open.find(')')
        {
            let payload_str = after_open.get(..close_pos).unwrap_or("");
            let consumed = 1 + prefix.len() + close_pos + 1;
            let full_tok = full_ir
                .get(sign_idx..sign_idx + consumed)
                .unwrap_or(payload_str);
            let converted = convert_special_fp_token(
                full_tok,
                is_neg,
                SpecialFpKind::NaNPayload {
                    signaling,
                    hex: payload_str,
                },
                active_fp,
            )?;
            return Ok(Some((consumed, converted)));
        }
    }

    Ok(None)
}
