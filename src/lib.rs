[report]
# Tarpaulin configuration for accurate coverage reporting
out = ["Html", "Lcov", "Stdout"]
output-dir = "coverage"

[run]
# Run all tests
all-features = true
workspace = true

# Exclude test code from coverage
exclude-files = []

# Count branches for more accurate coverage
count-branches = true

# NOTE: For network-incident operations, no specific coverage exclusions are currently required.
