# Agents.md

## Setup commands

You must check ~.cargo/config.toml for building instructions, environment setup alias.

## Code style

- Adhere to both Rust and Verus coding style (using `#[verus_spec(...)]`).
- Do not add `#[verifier::external_body]` carelessly unless instructed or necessary. Ask the user when adding these annotations.
