# Key State Machine

**Module:** `KERI.KeyState`

## Key state

The key state is the cumulative result of processing a KEL from inception through all subsequent events:

| Field | Type | Meaning |
|-------|------|---------|
| `prefix` | SAID | Identifier (immutable after inception) |
| `sequenceNumber` | Nat | Current sequence number |
| `lastDigest` | Digest | Digest of the most recent event |
| `signingThreshold` | Nat | Required signature count |
| `keys` | List Key | Current signing keys |
| `nextThreshold` | Nat | Threshold for next key set |
| `nextKeys` | List Digest | Commitments to next keys |
| `witnessThreshold` | Nat | Required witness receipt count |
| `witnesses` | List Key | Current witness set |

## State transitions

```mermaid
stateDiagram-v2
    [*] --> KeyState: Icp (initialState)
    KeyState --> KeyState: Rot (rotate keys)
    KeyState --> KeyState: Ixn (anchor data)
    KeyState --> KeyState: Rct (no-op)

    note right of KeyState
        Guards checked on every transition:
        - seqNum = prev + 1
        - prefix matches
        - not Icp
    end note
```

### `initialState`

Creates the initial key state from an inception event. Requires:

- Sequence number = 0
- No prior digest

### `applyEvent`

```mermaid
graph TD
    E[Event] --> CHK_SEQ{"seqNum =<br/>state.seqNum + 1?"}
    CHK_SEQ -->|no| NONE1[none]
    CHK_SEQ -->|yes| CHK_PFX{"prefix<br/>matches?"}
    CHK_PFX -->|no| NONE2[none]
    CHK_PFX -->|yes| CHK_TYPE{"event type?"}
    CHK_TYPE -->|Icp| NONE3["none (rejected)"]
    CHK_TYPE -->|Rot| ROT["Update keys,<br/>next-key commitments,<br/>witnesses"]
    CHK_TYPE -->|Ixn| IXN["Update seqNum,<br/>lastDigest"]
    CHK_TYPE -->|Rct| RCT["Return state<br/>unchanged"]
```

Applies a non-inception event to an existing state. Validates:

1. Sequence number = current + 1
2. Prefix matches
3. Event type is not inception

Then updates the state according to the event type:

- **Rotation**: replaces keys, next-key commitments, updates witnesses
- **Interaction**: increments sequence number, updates last digest
- **Receipt**: no-op (state unchanged)

## Proven invariants

### Initialization

- **`initial_state_seq_zero`** — The initial state always has sequence number 0
- **`initial_state_prefix`** — The initial state's prefix matches the inception event's prefix

### Transition guards

- **`apply_rejects_inception`** — You cannot apply an inception event to an existing state. Inception is only valid as the first event.
- **`apply_checks_sequence`** — A successful `applyEvent` requires `e.sequenceNumber = ks.sequenceNumber + 1`. Events cannot be applied out of order.
- **`apply_checks_prefix`** — A successful `applyEvent` requires the event's prefix to match the state's prefix. Events for a different identifier are rejected.

### State updates

- **`receipt_neutral`** — Receipt events leave the key state unchanged. They are acknowledgments, not mutations.
- **`apply_updates_sequence`** — For non-receipt events, a successful application increments the sequence number by exactly 1.
