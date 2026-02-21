/-
  KERI.Crypto — Abstract cryptographic primitives

  Axiomatized types for digests, signatures, and keys.
  Same pattern as kelgroups: abbreviations over Nat for
  decidable equality without concrete implementations.
-/

namespace KERI.Crypto

-- ============================================================
-- Abstract types
-- ============================================================

/-- Abstract digest (hash output). -/
abbrev Digest := Nat

/-- Self-Addressing Identifier. -/
abbrev SAID := Nat

/-- Abstract digital signature. -/
abbrev Signature := Nat

/-- Abstract public key. -/
abbrev Key := Nat

/-- Abstract secret key. -/
abbrev SecretKey := Nat

-- ============================================================
-- Abstract operations (opaque for axiomatization)
-- ============================================================

/-- Cryptographic hash function. -/
opaque hash : Nat → Digest

/-- Sign a message with a secret key. -/
opaque sign : SecretKey → Nat → Signature

/-- Verify a signature against a public key and message. -/
opaque verify : Key → Nat → Signature → Bool

/-- Derive a public key from a secret key. -/
opaque derivePublic : SecretKey → Key

/-- Compute a key commitment (hash of the public key). -/
opaque commitKey : Key → Digest

/-- Verify a key commitment. -/
opaque verifyCommitment : Key → Digest → Bool

-- ============================================================
-- Axioms (crypto assumptions)
-- ============================================================

/-- Signing with sk and verifying with the derived pk succeeds. -/
axiom sign_verify (sk : SecretKey) (msg : Nat) :
  verify (derivePublic sk) msg (sign sk msg) = true

/-- Hash is deterministic. -/
axiom hash_deterministic (x : Nat) : hash x = hash x

/-- commitKey is deterministic. -/
axiom commit_deterministic (k : Key) : commitKey k = commitKey k

/-- verifyCommitment succeeds for correctly committed keys. -/
axiom commit_verify (k : Key) : verifyCommitment k (commitKey k) = true

-- ============================================================
-- Theorems
-- ============================================================

/-- Commitment is a function: same input gives same output. -/
theorem commitment_deterministic (k : Key) :
    commitKey k = commitKey k :=
  rfl

/-- Verification succeeds for correctly committed keys. -/
theorem commitment_verify_correct (k : Key) :
    verifyCommitment k (commitKey k) = true :=
  commit_verify k

/-- Signature produced by sign is always verifiable with the
    corresponding public key. -/
theorem sign_then_verify (sk : SecretKey) (msg : Nat) :
    verify (derivePublic sk) msg (sign sk msg) = true :=
  sign_verify sk msg

end KERI.Crypto
