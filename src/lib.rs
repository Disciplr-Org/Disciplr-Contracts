#![cfg_attr(not(test), no_std)]
#![allow(clippy::too_many_arguments)]

use soroban_sdk::{contract, contractimpl, contracttype, token, Address, BytesN, Env, Symbol};

#[contracttype]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum VaultStatus {
    Active = 0,
    Completed = 1,
    Failed = 2,
    Cancelled = 3,
}

#[contracttype]
pub struct ProductivityVault {
    pub token: Address,
    pub creator: Address,
    pub amount: i128,
    pub start_timestamp: u64,
    pub end_timestamp: u64,
    pub milestone_hash: BytesN<32>,
    pub verifier: Option<Address>,
    pub success_destination: Address,
    pub failure_destination: Address,
    pub status: VaultStatus,
}

#[contracttype]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum DataKey {
    Vault(u32),
    NextId,
}

#[contract]
pub struct DisciplrVault;

#[contractimpl]
impl DisciplrVault {
    /// Create a new productivity vault. Caller must have approved token transfer to this contract.
    pub fn create_vault(
        env: Env,
        token: Address,
        creator: Address,
        amount: i128,
        start_timestamp: u64,
        end_timestamp: u64,
        milestone_hash: BytesN<32>,
        verifier: Option<Address>,
        success_destination: Address,
        failure_destination: Address,
    ) -> u32 {
        creator.require_auth();
        let contract = env.current_contract_address();
        token::Client::new(&env, &token).transfer_from(&contract, &creator, &contract, &amount);
        let next_id: u32 = env.storage().instance().get(&DataKey::NextId).unwrap_or(0);
        let vault_id = next_id;
        env.storage()
            .instance()
            .set(&DataKey::NextId, &(next_id + 1));
        let vault = ProductivityVault {
            token: token.clone(),
            creator: creator.clone(),
            amount,
            start_timestamp,
            end_timestamp,
            milestone_hash,
            verifier,
            success_destination,
            failure_destination,
            status: VaultStatus::Active,
        };
        env.storage()
            .instance()
            .set(&DataKey::Vault(vault_id), &vault);
        env.events()
            .publish((Symbol::new(&env, "vault_created"), vault_id), vault);
        vault_id
    }

    /// Verifier (or authorized party) validates milestone completion.
    pub fn validate_milestone(env: Env, vault_id: u32) -> bool {
        // TODO: check vault exists, status is Active, caller is verifier, timestamp < end
        // TODO: transfer USDC to success_destination, set status Completed
        env.events()
            .publish((Symbol::new(&env, "milestone_validated"), vault_id), ());
        true
    }

    /// Release funds to success destination (called after validation or by deadline logic).
    pub fn release_funds(_env: Env, _vault_id: u32) -> bool {
        // TODO: require status Active, transfer to success_destination, set Completed
        true
    }

    /// Redirect funds to failure destination (e.g. after deadline without validation).
    pub fn redirect_funds(_env: Env, _vault_id: u32) -> bool {
        // TODO: require status Active and past end_timestamp, transfer to failure_destination, set Failed
        true
    }

    /// Cancel vault and return funds to creator (if allowed by rules).
    pub fn cancel_vault(env: Env, vault_id: u32) -> bool {
        let mut vault: ProductivityVault = env
            .storage()
            .instance()
            .get(&DataKey::Vault(vault_id))
            .unwrap_or_else(|| panic!("vault not found"));
        vault.creator.require_auth();
        if vault.status != VaultStatus::Active {
            panic!("vault not active");
        }
        let contract = env.current_contract_address();
        let amount = vault.amount;
        let creator = vault.creator.clone();
        let token = vault.token.clone();
        let token_client = token::Client::new(&env, &token);
        token_client.transfer(&contract, &creator, &amount);
        vault.status = VaultStatus::Cancelled;
        env.storage()
            .instance()
            .set(&DataKey::Vault(vault_id), &vault);
        env.events()
            .publish((Symbol::new(&env, "vault_cancelled"), vault_id), ());
        true
    }

    /// Return current vault state for a given vault id.
    pub fn get_vault_state(env: Env, vault_id: u32) -> Option<ProductivityVault> {
        env.storage().instance().get(&DataKey::Vault(vault_id))
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use soroban_sdk::testutils::Address as _;
    use soroban_sdk::{contract, contractimpl, contracttype, token, String};

    #[contracttype]
    #[derive(Clone, Debug, Eq, PartialEq)]
    enum MockTokenKey {
        Balance(Address),
        Allowance(Address, Address),
    }

    #[contract]
    pub struct MockToken;

    #[contractimpl]
    impl MockToken {
        pub fn mint(env: Env, to: Address, amount: i128) {
            let balance: i128 = env
                .storage()
                .instance()
                .get(&MockTokenKey::Balance(to.clone()))
                .unwrap_or(0);
            env.storage()
                .instance()
                .set(&MockTokenKey::Balance(to), &(balance + amount));
        }

        pub fn balance(env: Env, id: Address) -> i128 {
            env.storage()
                .instance()
                .get(&MockTokenKey::Balance(id))
                .unwrap_or(0)
        }

        pub fn approve(
            env: Env,
            from: Address,
            spender: Address,
            amount: i128,
            _expiration_ledger: u32,
        ) {
            env.storage()
                .instance()
                .set(&MockTokenKey::Allowance(from, spender), &amount);
        }

        pub fn allowance(env: Env, from: Address, spender: Address) -> i128 {
            env.storage()
                .instance()
                .get(&MockTokenKey::Allowance(from, spender))
                .unwrap_or(0)
        }

        pub fn transfer(env: Env, from: Address, to: Address, amount: i128) {
            from.require_auth();
            let from_balance: i128 = env
                .storage()
                .instance()
                .get(&MockTokenKey::Balance(from.clone()))
                .unwrap_or(0);
            let to_balance: i128 = env
                .storage()
                .instance()
                .get(&MockTokenKey::Balance(to.clone()))
                .unwrap_or(0);
            env.storage()
                .instance()
                .set(&MockTokenKey::Balance(from), &(from_balance - amount));
            env.storage()
                .instance()
                .set(&MockTokenKey::Balance(to), &(to_balance + amount));
        }

        pub fn transfer_from(env: Env, spender: Address, from: Address, to: Address, amount: i128) {
            spender.require_auth();
            let allow: i128 = env
                .storage()
                .instance()
                .get(&MockTokenKey::Allowance(from.clone(), spender.clone()))
                .unwrap_or(0);
            if allow < amount {
                panic!("insufficient allowance");
            }
            env.storage().instance().set(
                &MockTokenKey::Allowance(from.clone(), spender),
                &(allow - amount),
            );
            let from_balance: i128 = env
                .storage()
                .instance()
                .get(&MockTokenKey::Balance(from.clone()))
                .unwrap_or(0);
            let to_balance: i128 = env
                .storage()
                .instance()
                .get(&MockTokenKey::Balance(to.clone()))
                .unwrap_or(0);
            env.storage()
                .instance()
                .set(&MockTokenKey::Balance(from), &(from_balance - amount));
            env.storage()
                .instance()
                .set(&MockTokenKey::Balance(to), &(to_balance + amount));
        }

        pub fn burn(env: Env, from: Address, amount: i128) {
            from.require_auth();
            let balance: i128 = env
                .storage()
                .instance()
                .get(&MockTokenKey::Balance(from.clone()))
                .unwrap_or(0);
            env.storage()
                .instance()
                .set(&MockTokenKey::Balance(from), &(balance - amount));
        }

        pub fn burn_from(env: Env, spender: Address, from: Address, amount: i128) {
            spender.require_auth();
            let allow: i128 = env
                .storage()
                .instance()
                .get(&MockTokenKey::Allowance(from.clone(), spender.clone()))
                .unwrap_or(0);
            if allow < amount {
                panic!("insufficient allowance");
            }
            env.storage().instance().set(
                &MockTokenKey::Allowance(from.clone(), spender),
                &(allow - amount),
            );
            let balance: i128 = env
                .storage()
                .instance()
                .get(&MockTokenKey::Balance(from.clone()))
                .unwrap_or(0);
            env.storage()
                .instance()
                .set(&MockTokenKey::Balance(from), &(balance - amount));
        }

        pub fn decimals(env: Env) -> u32 {
            let _ = env;
            6
        }

        pub fn name(env: Env) -> String {
            String::from_str(&env, "Test Token")
        }

        pub fn symbol(env: Env) -> String {
            String::from_str(&env, "TEST")
        }
    }

    /// cancel_vault returns funds to creator and sets status to Cancelled.
    #[test]
    fn cancel_vault_returns_funds_to_creator_and_sets_cancelled() {
        let env = Env::default();
        let token_id = env.register(test::MockToken, ());
        let vault_contract_id = env.register(DisciplrVault, ());

        let creator = Address::generate(&env);
        let amount: i128 = 10_000_000; // 10 units with 6 decimals
        let start_ts: u64 = 1000;
        let end_ts: u64 = 2000;
        let milestone_hash = BytesN::from_array(&env, &[0u8; 32]);
        let success_dest = Address::generate(&env);
        let failure_dest = Address::generate(&env);

        // Mint tokens to creator and approve vault contract to spend
        let mock_token = test::MockTokenClient::new(&env, &token_id);
        mock_token.mint(&creator, &amount);
        let exp_ledger = env.ledger().sequence() + 1000;
        mock_token.approve(&creator, &vault_contract_id, &amount, &exp_ledger);

        let vault_client = DisciplrVaultClient::new(&env, &vault_contract_id);
        let token_client = token::Client::new(&env, &token_id);

        assert_eq!(
            token_client.balance(&creator),
            amount,
            "creator should have minted amount before create_vault"
        );

        // Mock auth so creator.require_auth() and token transfer_from(spender) succeed in tests
        env.mock_all_auths();

        // Create vault as creator (funds pulled from creator to contract)
        let vault_id = vault_client.create_vault(
            &token_id,
            &creator,
            &amount,
            &start_ts,
            &end_ts,
            &milestone_hash,
            &None::<Address>,
            &success_dest,
            &failure_dest,
        );

        assert_eq!(
            token_client.balance(&creator),
            0,
            "creator balance should be 0 after create_vault (funds locked in vault)"
        );

        // Cancel vault as creator (returns funds to creator)
        vault_client.cancel_vault(&vault_id);

        let creator_balance_after = token_client.balance(&creator);
        assert_eq!(
            creator_balance_after, amount,
            "cancel_vault must return vault amount to creator"
        );

        let state = vault_client.get_vault_state(&vault_id);
        let vault = state.expect("vault should exist");
        assert_eq!(
            vault.status,
            VaultStatus::Cancelled,
            "vault status must be Cancelled after cancel_vault"
        );
        assert_eq!(vault.creator, creator);
        assert_eq!(vault.amount, amount);
    }
}
