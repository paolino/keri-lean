# Roadmap

Features needed in keri-lean (and their keri-hs / keri-purs implementations)
to support the [kelgroups roadmap](https://github.com/paolino/kelgroups/blob/main/docs/docs/roadmap.md).

## Current state

### Formalized in keri-lean

| Module | What it covers |
|---|---|
| `KERI.Crypto` | Abstract primitives: keys, signatures, digests, hashing (4 axioms) |
| `KERI.CESR` | Derivation codes, encoding sizes, roundtrip property |
| `KERI.Event` | Generic `KELEvent α`, KERI `EventPayload` (Icp/Rot/Ixn/Rct), event classification |
| `KERI.SAID` | SAID verification: `verifySAID`, `computeSAID`, `claimedDigest` (2 axioms, 3 theorems) |
| `KERI.KeyState` | State machine: `initialState`, `applyEvent` with SAID guard, pre-rotation (8 theorems) |
| `KERI.KEL` | Hash chain validity, replay, signature threshold (5 theorems) |
| `KERI.PreRotation` | Commitment scheme: `commitKey`, `verifyPreRotation` (3 theorems) |

### Implemented in keri-hs / keri-purs

| Feature | keri-hs module | keri-purs module |
|---|---|---|
| CESR encoding/decoding | `Keri.Cesr.*` | `Keri.Cesr.*` |
| Ed25519 signatures | `Keri.Crypto.Ed25519` | `Keri.Crypto.Ed25519` |
| Blake3 digest (via Blake2b) | `Keri.Crypto.Digest` | `Keri.Crypto.Digest` |
| Event creation (icp/rot/ixn) | `Keri.Event.Inception`, `.Rotation`, `.Interaction` | same |
| SAID verification | `Keri.Crypto.SAID` | `Keri.Crypto.SAID` |
| KEL append + replay | `Keri.Kel.Append`, `Keri.Kel.Replay` | same |
| Key state machine | `Keri.KeyState` | `Keri.KeyState` |
| Signature verification | `Keri.KeyState.Verify` | `Keri.KeyState.Verify` |
| Pre-rotation commitment | `Keri.KeyState.PreRotation` | `Keri.KeyState.PreRotation` |

## Roadmap

### 1. Identifier creation helper (kelgroups Step 10)

**Status:** not started
**Needed for:** KEL-managed identities in kelgroups

Currently the caller has to orchestrate `mkInception` + sign + `append emptyKel`
manually. Provide a convenience function that creates an inception event, signs
it, appends to a new KEL, and returns the prefix + KEL.

**keri-hs / keri-purs:**

- New function in `Keri.Kel`: `createIdentifier :: KeyPair -> InceptionConfig -> Either String (Prefix, Kel)`
- Wraps the inception + sign + append sequence

**keri-lean:**

- No new formalization needed — `initialState` and `replay` already cover inception

### 2. Witness threshold enforcement (kelgroups Step 12)

**Status:** not started
**Needed for:** witness receipts

`InceptionConfig` has `icWitnesses` and `icWitnessThreshold`, and `KeyState`
stores them, but `append` ignores witness threshold entirely. Receipt events
(`Rct`) exist but are not collected or verified against witness keys.

**keri-lean:**

- Formalize `witnessThresholdMet`: receipt count from distinct witnesses
  meets `stateWitnessThreshold`
- Add `witnessThresholdMet` as a guard in event confirmation (separate from
  `append` — events can be appended but not confirmed until receipted)
- Theorem: confirmed events have sufficient witness receipts

**keri-hs / keri-purs:**

- Track pending receipts per event in KEL management
- `collectReceipt :: Kel -> Receipt -> Either String Kel` — verify receipt
  signature against witness key, accumulate
- `isConfirmed :: Kel -> SequenceNumber -> Bool` — check if witness threshold
  met for a given event
- Enforce witness threshold in `append` (configurable: strict mode rejects
  unreceipted events, permissive mode accepts but marks unconfirmed)

### 3. Receipt verification (kelgroups Step 12)

**Status:** not started
**Needed for:** witness receipts

Receipt events carry a receipted event digest and a witness signature. Need
to verify that the receipt references a real event and the signature matches
a configured witness key.

**keri-lean:**

- Formalize `receiptValid`: receipt digest matches an event in the KEL,
  receipt signer is in `stateWitnesses`
- Currently `receipt_neutral` proves receipts don't change state; add
  `receipt_valid_implies_witness` — valid receipt signer must be a witness

**keri-hs / keri-purs:**

- `verifyReceipt :: KeyState -> Kel -> SignedEvent -> Either String ()` —
  check receipt references existing event, signer is a witness, signature valid

### 4. Witness rotation (kelgroups Step 12)

**Status:** not started
**Needed for:** witness lifecycle management

`RotationConfig` has `rcWitnessConfig` (add/remove witnesses) but `applyEvent`
ignores it — `KeyState.stateWitnesses` is set at inception and never updated.

**keri-lean:**

- Update `applyEvent` for rotation to apply `WitnessConfig` changes to
  `stateWitnesses`
- Theorem: `rotation_updates_witnesses` — after rotation with witness config,
  `stateWitnesses` reflects the additions and removals

**keri-hs / keri-purs:**

- Update `applyEvent` rotation case to apply witness adds/removes
- Tests: witness rotation round-trip, receipt rejected after witness removal

### 5. Duplicity detection (kelgroups Step 13)

**Status:** not started
**Needed for:** detecting compromised server publishing conflicting KELs

No mechanism exists to detect two valid but conflicting KELs for the same
prefix (same inception, diverging at some sequence number).

**keri-lean:**

- Define `duplicitous`: two KELs share the same prefix (inception event)
  but contain different events at some sequence number
- Theorem: `hashChainValid` + same inception + different event at sequence N
  implies different digest chains from N onward (divergence is permanent)
- Theorem: a duplicitous pair cannot both be valid if witnesses are honest
  (at least one receipt set must be forged)

**keri-hs / keri-purs:**

- `detectDuplicity :: Kel -> Kel -> Maybe DuplicityEvidence` — compare two
  KELs for the same prefix, return the first divergence point
- `DuplicityEvidence` contains: prefix, sequence number, the two conflicting
  events, and their respective receipt sets

## Companion projects

| Project | Role | Link |
|---|---|---|
| **keri-hs** | Haskell implementation | [github.com/paolino/keri-hs](https://github.com/paolino/keri-hs) |
| **keri-purs** | PureScript implementation (browser) | [github.com/paolino/keri-purs](https://github.com/paolino/keri-purs) |
| **kelgroups** | Governance layer (consumer) | [github.com/paolino/kelgroups](https://github.com/paolino/kelgroups) |

## Not needed

These KERI features are not required by kelgroups:

- **Weighted thresholds** — kelgroups uses simple admin majority
- **Delegated identifiers** — no hierarchical delegation
- **OOBI protocol** — centralized server stores all participant KELs
- **Indirect mode networking** — direct HTTP
- **Out-of-order event escrow** — nice to have but not blocking
