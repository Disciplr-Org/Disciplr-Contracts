import os

lib_path = "src/lib.rs"
with open(lib_path, "r") as f:
    content = f.read()

new_tests = """
    #[test]
    #[should_panic(expected = "Error(Contract, 3)")]
    fn test_double_cancel_fails_142() {
        let setup = TestSetup::new();
        setup.env.mock_all_auths();
        let vault_id = setup.create_default_vault();
        setup.client().cancel_vault(&vault_id, &setup.usdc_client().address);
        setup.client().cancel_vault(&vault_id, &setup.usdc_client().address);
    }

    #[test]
    #[should_panic(expected = "Error(Contract, 4)")]
    fn test_redirect_exact_deadline_fails_150() {
        let setup = TestSetup::new();
        setup.env.mock_all_auths();
        let vault_id = setup.create_default_vault();
        let vault = setup.client().get_vault_state(&vault_id).unwrap();
        setup.env.ledger().set_timestamp(vault.end_timestamp);
        setup.client().redirect_funds(&vault_id, &setup.usdc_client().address);
    }
"""

# Insert before the last closing brace of the file (which closes mod test)
last_brace_index = content.rfind('}')
if last_brace_index != -1:
    content = content[:last_brace_index] + new_tests + "\n}\n"
    with open(lib_path, "w") as f:
        f.write(content)
    print("Tests added successfully!")
else:
    print("Failed to add tests.")
