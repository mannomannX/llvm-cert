use std::fmt;
use std::path::PathBuf;

/// Structured error type for `ir-bridge` operations (zero panics across library and CLI).
#[derive(Debug)]
pub enum BridgeError {
    Io {
        path: PathBuf,
        source: std::io::Error,
    },
    ManifestJson(serde_json::Error),
    InvalidFloatLiteral {
        token: String,
        reason: &'static str,
    },
    UnterminatedBlockComment,
    MalformedModule {
        detail: String,
    },
    FastPathIneligible {
        reasons: Vec<String>,
    },
    MissingVerifiedSlice {
        function_name: String,
    },
    VerificationToolFailed {
        tool: String,
        stderr: String,
    },
}

impl fmt::Display for BridgeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Io { path, source } => {
                write!(f, "I/O error on `{}`: {source}", path.display())
            }
            Self::ManifestJson(err) => write!(f, "manifest JSON error: {err}"),
            Self::InvalidFloatLiteral { token, reason } => {
                write!(
                    f,
                    "invalid LLVM 23 floating-point literal `{token}`: {reason}"
                )
            }
            Self::UnterminatedBlockComment => {
                write!(
                    f,
                    "unterminated C-style `/* ... */` block comment in LLVM IR"
                )
            }
            Self::MalformedModule { detail } => write!(f, "malformed LLVM IR module: {detail}"),
            Self::FastPathIneligible { reasons } => {
                write!(
                    f,
                    "Fast-Path target IR requires Safe-Path fallback: {}",
                    reasons.join("; ")
                )
            }
            Self::MissingVerifiedSlice { function_name } => {
                write!(f, "missing verified function slice for `@{function_name}`")
            }
            Self::VerificationToolFailed { tool, stderr } => {
                write!(f, "post-merge verification failed via `{tool}`: {stderr}")
            }
        }
    }
}

impl std::error::Error for BridgeError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Io { source, .. } => Some(source),
            Self::ManifestJson(err) => Some(err),
            _ => None,
        }
    }
}
