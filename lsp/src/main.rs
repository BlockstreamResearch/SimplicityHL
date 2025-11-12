#![warn(clippy::all, clippy::pedantic)]

mod backend;
mod completion;
mod error;
mod function;
mod utils;

use backend::Backend;
use tower_lsp_server::{LspService, Server};

#[tokio::main]
async fn main() {
    env_logger::init();
    let (stdin, stdout) = (tokio::io::stdin(), tokio::io::stdout());

    let (service, socket) = LspService::new(Backend::new);
    Server::new(stdin, stdout, socket).serve(service).await;
}
