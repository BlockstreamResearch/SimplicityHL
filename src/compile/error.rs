#[derive(Debug, thiserror::Error, Clone)]
pub enum Error {
    #[error("Variable `{identifier}` is not defined")]
    UndefinedVariable { identifier: crate::str::Identifier },

    #[error("Simplicity type error")]
    TypeError(#[from] simplicity::types::Error),
}
