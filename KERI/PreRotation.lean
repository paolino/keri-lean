/-
  KERI.PreRotation — Pre-rotation commitment scheme

  Models the KERI pre-rotation mechanism where next-key
  commitments are published in advance and verified
  during rotation.
-/
import KERI.Crypto

namespace KERI.PreRotation

open KERI.Crypto

-- ============================================================
-- Commitment verification
-- ============================================================

/-- Verify that a list of keys matches a list of commitments.
    Each key's commitment must equal the corresponding entry. -/
def verifyPreRotation (keys : List Key) (commitments : List Digest)
    : Bool :=
  (keys.length == commitments.length) &&
  (keys.zip commitments).all fun (k, c) => verifyCommitment k c

-- ============================================================
-- Theorems
-- ============================================================

/-- Commitment roundtrip: verifyCommitment succeeds for a
    correctly committed key. -/
theorem commit_verify_roundtrip (k : Key) :
    verifyCommitment k (commitKey k) = true :=
  commit_verify k

/-- Empty keys and empty commitments pass verification. -/
theorem verify_prerotation_empty :
    verifyPreRotation [] [] = true := by
  simp [verifyPreRotation]

/-- A single correctly committed key passes verification. -/
theorem verify_prerotation_singleton (k : Key) :
    verifyPreRotation [k] [commitKey k] = true := by
  simp [verifyPreRotation, List.zip, List.all, commit_verify]

end KERI.PreRotation
