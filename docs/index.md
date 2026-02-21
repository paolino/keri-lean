# keri-lean

Lean 4 formalization of [KERI](https://keri.one/) (Key Event Receipt Infrastructure) protocol invariants.

This project extracts and proves the core invariants of KERI — the protocol for decentralized key management — as machine-checked theorems in Lean 4. The formalization covers:

- **Cryptographic primitives** — axiomatized abstract types for digests, signatures, and keys
- **CESR encoding** — derivation code sizes and roundtrip properties
- **Event structure** — generic hash-chained event logs parameterized over payloads
- **Key state machine** — transition rules and their correctness
- **KEL integrity** — hash chain validity and replay properties
- **Pre-rotation** — commitment scheme for forward-secure key rotation

## Companion projects

| Project | Role |
|---------|------|
| [keri-hs](https://github.com/paolino/keri-hs) | Haskell implementation of KERI primitives |
| [kelgroups](https://github.com/paolino/kelgroups) | Governance layer built on KERI (imports keri-lean) |

## Build

```
lake build
```

Requires Lean 4.27.0 (version pinned in `lean-toolchain`).

## No sorry, no custom axioms

All theorems compile without `sorry`. The only axioms are:

- Standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`)
- Explicitly declared crypto axioms (signature verification, hash determinism, commitment correctness) — these model assumptions about the underlying cryptographic implementations that cannot be proven without concrete algorithms
