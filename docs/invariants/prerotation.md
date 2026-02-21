# Pre-Rotation

**Module:** `KERI.PreRotation`

## The pre-rotation mechanism

Pre-rotation is KERI's key innovation for forward-secure key management. The idea:

1. At inception (or rotation), you publish **commitments** to your next key set — `commitKey(nextKey)` for each key
2. When you rotate, you reveal the actual keys and prove they match the commitments
3. An attacker who compromises your current keys **cannot** rotate to their own keys because they don't know which keys match the published commitments

This creates a one-time-pad-like protection: even with full access to current signing keys, an attacker cannot forge a valid rotation without the pre-committed next keys.

## Verification

`verifyPreRotation` checks two things:

1. **Length match**: the number of revealed keys equals the number of commitments
2. **Commitment match**: each key's commitment equals the corresponding published commitment

```
def verifyPreRotation (keys : List Key) (commitments : List Digest) : Bool :=
  keys.length = commitments.length
  && keys.zip commitments |>.all fun (k, c) => verifyCommitment k c
```

## Proven invariants

### `commit_verify_roundtrip`

> `verifyCommitment k (commitKey k) = true`

The fundamental soundness property: if you commit to a key and later reveal it, the verification succeeds. This follows directly from the `commit_verify` axiom in `Crypto`.

### `verify_prerotation_length`

> If `verifyPreRotation` succeeds, then `keys.length = commitments.length`.

Pre-rotation requires exactly as many keys as there were commitments. You can't add or remove keys during rotation without them being pre-committed.

### `verify_prerotation_empty`

> Empty key sets trivially pass verification.

Base case for inductive reasoning.

### `verify_prerotation_singleton`

> A single correctly committed key passes verification.

The minimal non-trivial case.

### `verify_prerotation_correct`

> If all keys are correctly committed (`commitments = keys.map commitKey`), verification passes.

This is the completeness property: the happy path always works. Combined with the length check, it shows that `verifyPreRotation` accepts exactly the right inputs.
