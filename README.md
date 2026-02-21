# keri-lean

Lean 4 formalization of [KERI](https://keri.one/) protocol invariants.

**[Documentation](https://paolino.github.io/keri-lean/)**

## Modules

- `KERI.Crypto` — Abstract cryptographic primitives and axioms
- `KERI.CESR` — CESR encoding/decoding properties
- `KERI.Event` — KEL event types and structure
- `KERI.KeyState` — Key state machine transitions
- `KERI.KEL` — Hash chain and log integrity invariants
- `KERI.PreRotation` — Pre-rotation commitment scheme

## Build

```
nix develop -c just ci
```

Or without nix (requires elan):

```
lake build
```

## License

[Apache-2.0](LICENSE)
