import os

lib_path = "src/lib.rs"
with open(lib_path, "r") as f:
    content = f.read()

# Patch 1: #117 Enforce authorization on release_funds
old_release = """    pub fn release_funds(env: Env, vault_id: u32, usdc_token: Address) -> Result<bool, Error> {
        let vault_key = DataKey::Vault(vault_id);
        let mut vault: ProductivityVault = env
            .storage()
            .instance()
            .get(&vault_key)
            .ok_or(Error::VaultNotFound)?;"""

new_release = """    pub fn release_funds(env: Env, vault_id: u32, usdc_token: Address) -> Result<bool, Error> {
        let vault_key = DataKey::Vault(vault_id);
        let mut vault: ProductivityVault = env
            .storage()
            .instance()
            .get(&vault_key)
            .ok_or(Error::VaultNotFound)?;

        vault.creator.require_auth();"""

# Patch 2: #150 Exact deadline boundary exclusive for redirect
old_redirect = """        if env.ledger().timestamp() < vault.end_timestamp {
            return Err(Error::InvalidTimestamp); // Too early to redirect
        }"""

new_redirect = """        if env.ledger().timestamp() <= vault.end_timestamp {
            return Err(Error::InvalidTimestamp); // Too early to redirect
        }"""

if old_release in content and old_redirect in content:
    content = content.replace(old_release, new_release)
    content = content.replace(old_redirect, new_redirect)
    with open(lib_path, "w") as f:
        f.write(content)
    print("Source patched successfully!")
else:
    print("Error: Could not find target strings to replace.")
