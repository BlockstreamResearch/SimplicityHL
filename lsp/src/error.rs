use std::num::TryFromIntError;

use thiserror::Error;

use tower_lsp_server::jsonrpc::Error;
use tower_lsp_server::lsp_types::Uri;

/// Custom error type for LSP server.
#[derive(Debug, Clone, Error)]
pub enum LspError {
    /// An error during the conversion of different types.
    #[error("Conversion failed: {0}")]
    ConversionFailed(String),

    /// An error during the conversion of integer types.
    #[error("Conversion failed: {0}")]
    IntegerConversionFailed(#[from] TryFromIntError),

    /// Failed to find function inside `functions` map.
    #[error("Function not found: {0}")]
    FunctionNotFound(String),

    /// Failed to find call inside function.
    #[error("Call not found: {0}")]
    CallNotFound(String),

    /// Failed to find given document inside `documents` map.
    #[error("Document not found: {0:?}")]
    DocumentNotFound(Uri),

    /// A generic or unexpected internal error.
    #[error("Internal error: {0}")]
    Internal(String),
}

impl LspError {
    /// Return error code for error.
    ///
    /// Error code is needed for [`tower_lsp_server::jsonrpc::Error`] to differentiate errors. It's
    /// recommended to use values from 1 to 5000.
    pub const fn code(&self) -> i64 {
        match self {
            LspError::ConversionFailed(_) => 1,
            LspError::FunctionNotFound(_) => 2,
            LspError::CallNotFound(_) => 3,
            LspError::DocumentNotFound(_) => 4,
            LspError::IntegerConversionFailed(_) => 5,
            LspError::Internal(_) => 100,
        }
    }
}

/// Convert [`LspError`] to [`tower_lsp_server::jsonrpc::Error`].
impl From<LspError> for Error {
    fn from(err: LspError) -> Self {
        Error {
            code: err.code().into(),
            message: err.to_string().into(),
            data: None,
        }
    }
}
