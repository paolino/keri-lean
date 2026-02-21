# keri-lean

Lean 4 formalization of KERI protocol invariants.

## Modules

- `KERI.Crypto` — Abstract cryptographic primitives and axioms
- `KERI.CESR` — CESR encoding/decoding properties
- `KERI.Event` — KEL event types and structure
- `KERI.KeyState` — Key state machine transitions
- `KERI.KEL` — Hash chain and log integrity invariants
- `KERI.PreRotation` — Pre-rotation commitment scheme

## Build

```
lake build
```

Requires Lean 4.27.0 (set via `lean-toolchain`).
