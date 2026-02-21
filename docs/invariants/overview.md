# Invariant Overview

KERI's security rests on a small set of invariants that must hold across all event processing. This formalization makes them explicit and machine-checked.

## Module dependency graph

```
Crypto ──┬── CESR
         ├── Event ──┬── KeyState
         │           └── KEL
         └── PreRotation
```

`Crypto` provides the abstract primitives. `Event` defines the generic event structure (shared with kelgroups). `KeyState`, `KEL`, and `PreRotation` build the KERI-specific invariants on top.

## Axioms vs theorems

We distinguish two categories:

**Axioms** are assumptions about the cryptographic layer that cannot be proven without a concrete implementation:

| Axiom | Module | Meaning |
|-------|--------|---------|
| `sign_verify` | Crypto | Signatures produced by `sign` are accepted by `verify` |
| `hash_deterministic` | Crypto | Hashing is a function |
| `commit_verify` | Crypto | `verifyCommitment(k, commitKey(k))` succeeds |
| `roundtrip_ax` | CESR | `decode(encode(p)) = p` for well-formed primitives |

**Theorems** are proven consequences that follow from the definitions and axioms:

| Count | Module | Examples |
|-------|--------|----------|
| 3 | Crypto | `sign_then_verify`, `commitment_verify_correct` |
| 7 | CESR | `ed25519_pub_total_length`, `roundtrip`, `primitive_size_valid` |
| 4 | Event | `inception_type`, `prefix_consistent_icp` |
| 7 | KeyState | `initial_state_seq_zero`, `apply_rejects_inception`, `receipt_neutral` |
| 5 | KEL | `singleton_chain_valid`, `kel_starts_with_inception`, `replay_inception_gives_initial` |
| 4 | PreRotation | `commit_verify_roundtrip`, `verify_prerotation_correct` |

## Relationship to kelgroups

The `KELEvent` structure and `hashChainValid` predicate were originally defined in kelgroups. This project extracts the generic KERI parts so that kelgroups (and any other KERI-based project) can depend on them via Lake's `require` mechanism.
