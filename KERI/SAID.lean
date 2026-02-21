/-
  KERI.SAID — Self-Addressing Identifier verification

  Models SAID computation and verification: events are
  serialized with a placeholder digest, hashed, and the
  result compared against the claimed digest field.
-/
import KERI.Crypto
import KERI.Event

namespace KERI.SAID

open KERI.Crypto
open KERI.Event

-- ============================================================
-- Abstract SAID operations
-- ============================================================

/-- Serialize an event with the digest field replaced by
    a placeholder (for SAID computation). -/
opaque serializeForSAID : KERIEvent → Nat

/-- Extract the claimed digest from an event's @d@ field. -/
opaque claimedDigest : KERIEvent → Digest

-- ============================================================
-- SAID computation and verification
-- ============================================================

/-- Compute the SAID of an event by hashing its
    placeholder-serialized form. -/
def computeSAID (e : KERIEvent) : Digest :=
  hash (serializeForSAID e)

/-- Verify that the claimed digest matches the computed SAID. -/
def verifySAID (e : KERIEvent) : Bool :=
  decide (computeSAID e = claimedDigest e)

-- ============================================================
-- Axioms
-- ============================================================

/-- Events constructed via the SAID protocol (serialize with
    placeholder, hash, set digest) pass verifySAID. -/
axiom said_creation_correct (e : KERIEvent)
    (h : claimedDigest e = computeSAID e) :
    verifySAID e = true

/-- For a verified inception event, the prefix equals the
    claimed digest (self-addressing property). -/
axiom inception_prefix_is_said (e : KERIEvent)
    (p : SAID) (st : Nat) (ks : List Key) (nt : Nat)
    (nks : List Digest) (wt : Nat) (ws : List Key)
    (hp : e.payload = .Icp p st ks nt nks wt ws)
    (hv : verifySAID e = true) :
    p = claimedDigest e

-- ============================================================
-- Theorems
-- ============================================================

/-- verifySAID succeeds when the claimed digest equals
    the computed SAID. -/
theorem verify_said_correct (e : KERIEvent)
    (h : claimedDigest e = computeSAID e) :
    verifySAID e = true :=
  said_creation_correct e h

/-- If verifySAID returns true then computeSAID equals
    claimedDigest. -/
theorem verify_said_implies_authentic (e : KERIEvent)
    (h : verifySAID e = true) :
    computeSAID e = claimedDigest e := by
  unfold verifySAID at h
  exact of_decide_eq_true h

/-- For a verified inception event, the prefix is the SAID. -/
theorem self_addressing_verified (e : KERIEvent)
    (p : SAID) (st : Nat) (ks : List Key) (nt : Nat)
    (nks : List Digest) (wt : Nat) (ws : List Key)
    (hp : e.payload = .Icp p st ks nt nks wt ws)
    (hv : verifySAID e = true) :
    p = computeSAID e := by
  have hpc := inception_prefix_is_said e p st ks nt nks wt ws hp hv
  have hauth := verify_said_implies_authentic e hv
  rw [hpc, hauth]

end KERI.SAID
