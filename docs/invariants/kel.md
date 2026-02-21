# KEL Integrity

**Module:** `KERI.KEL`

## Hash chain validity

The fundamental integrity property of any KEL is its hash chain: each event (except inception) links to its predecessor via a prior digest, and sequence numbers form a contiguous sequence starting from 0.

```
def hashChainValid (kel : KEL α) : Prop :=
  match kel with
  | [] => True
  | [e] => e.sequenceNumber = 0 ∧ e.priorDigest = none
  | e :: rest =>
    e.priorDigest.isSome
    ∧ (match rest.head? with
       | some prev => e.sequenceNumber = prev.sequenceNumber + 1
       | none => False)
    ∧ hashChainValid rest
```

This definition is recursive over the list (newest-first). The base cases are:

- **Empty list**: trivially valid
- **Single event**: must be inception (seq 0, no prior digest)
- **Cons**: must have a prior digest, sequence number one more than predecessor, and the rest must be valid

## Proven invariants

### `singleton_chain_valid`

> A single event with sequence number 0 and no prior digest forms a valid chain.

This is the base case: every KEL starts with a single inception event.

### `kel_starts_with_inception`

> In any valid non-empty KEL, there exists an event with sequence number 0 and no prior digest.

This proves that the inception event is always present — you can't have a valid KEL that starts mid-stream.

### `replay_empty_fails`

> Replaying an empty event list produces no state.

You need at least an inception event.

### `replay_inception_gives_initial`

> Replaying a single valid inception event produces the same state as `initialState`.

This connects the replay function to the initialization function.

### `threshold_zero_met`

> A signature threshold of 0 is satisfied by any number of signatures.

This handles the degenerate case (useful for testing).

## Replay function

`replay` processes events oldest-first:

1. The first event must be a valid inception (via `initialState`)
2. Each subsequent event is applied via `applyEvent`
3. Any failure short-circuits to `none`
