# Cryptographic Primitives

**Module:** `KERI.Crypto`

## Abstract types

All cryptographic types are abbreviations over `Nat`. This gives us decidable equality for free while keeping the formalization independent of any concrete implementation.

| Type | Meaning |
|------|---------|
| `Digest` | Hash output (e.g. Blake2b-256) |
| `SAID` | Self-Addressing Identifier |
| `Signature` | Digital signature (e.g. Ed25519) |
| `Key` | Public key |
| `SecretKey` | Secret (signing) key |

## Operations

| Operation | Signature | Purpose |
|-----------|-----------|---------|
| `hash` | `Nat → Digest` | Cryptographic hash |
| `sign` | `SecretKey → Nat → Signature` | Sign a message |
| `verify` | `Key → Nat → Signature → Bool` | Verify a signature |
| `derivePublic` | `SecretKey → Key` | Derive public key from secret |
| `commitKey` | `Key → Digest` | Compute key commitment |
| `verifyCommitment` | `Key → Digest → Bool` | Check key against commitment |

All operations are declared `opaque` — their implementations are not visible to the prover, ensuring theorems rely only on the stated axioms.

## Axioms

### `sign_verify`

> Signing with a secret key and verifying with the corresponding public key always succeeds.

```
verify (derivePublic sk) msg (sign sk msg) = true
```

This is the fundamental correctness assumption for any digital signature scheme.

### `commit_verify`

> A key always passes verification against its own commitment.

```
verifyCommitment k (commitKey k) = true
```

This models the pre-rotation commitment mechanism: if you publish `commitKey(k)` now, you can later reveal `k` and anyone can verify the commitment.

## Proven theorems

- **`commitment_deterministic`** — `commitKey` is a function (same input, same output)
- **`commitment_verify_correct`** — direct consequence of `commit_verify` axiom
- **`sign_then_verify`** — direct consequence of `sign_verify` axiom
