#!/bin/bash
set -e

# Disciplr Vault: Reproducible WASM Build Script
# This script ensures that the contract is built with consistent flags and locked dependencies.

PROJECT_ROOT=$(git rev-parse --show-toplevel)
cd "$PROJECT_ROOT"

echo "Checking for WASM target..."
if ! rustup target list --installed | grep -q wasm32-unknown-unknown; then
    echo "Installing wasm32-unknown-unknown target..."
    rustup target add wasm32-unknown-unknown
fi

echo "Building reproducible WASM binary..."
# --locked ensures we use the exact versions from Cargo.lock
# --target wasm32-unknown-unknown for Soroban compatibility
# --release uses optimized profile from Cargo.toml
cargo build --target wasm32-unknown-unknown --release --locked

echo "Build complete."
WASM_PATH="target/wasm32-unknown-unknown/release/disciplr_vault.wasm"
if [ -f "$WASM_PATH" ]; then
    SIZE=$(du -h "$WASM_PATH" | cut -f1)
    echo "Success! WASM binary generated: $WASM_PATH ($SIZE)"
else
    echo "Error: WASM binary not found at $WASM_PATH"
    exit 1
fi
