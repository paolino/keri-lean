# Build Lean proofs
build:
    lake build

# Check for sorry in Lean files
lint:
    @echo "Checking for sorry..."
    @! grep -rn 'sorry' --include='*.lean' KERI/ KERI.lean || (echo "FAIL: sorry found" && exit 1)
    @echo "No sorry found."

# Check axioms (only standard + declared crypto axioms)
axioms:
    @echo "Checking axioms..."
    lake env lean KERI.lean 2>&1 | grep -i 'axiom' || true

# Format check (verify no trailing whitespace)
format:
    @echo "Checking formatting..."
    @! grep -rPn '\t' --include='*.lean' KERI/ KERI.lean || true
    @! grep -rPn ' +$$' --include='*.lean' KERI/ KERI.lean || (echo "FAIL: trailing whitespace" && exit 1)
    @echo "Format OK."

# Full CI pipeline
ci: lint format build

# Build docs (uses mkdocs from nix shell)
build-docs:
    mkdocs build

# Serve docs locally (uses mkdocs from nix shell)
serve-docs:
    mkdocs serve

# Deploy docs to GitHub Pages
deploy-docs:
    mkdocs gh-deploy --force

# Clean build artifacts
clean:
    lake clean
    rm -rf site/
