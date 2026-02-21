/-
  KERI.Event — KEL event types and structure

  Generic KEL event structure extracted from kelgroups,
  plus KERI-specific event type classification.
-/
import KERI.Crypto

namespace KERI.Event

open KERI.Crypto

-- ============================================================
-- Generic KEL event (extracted from kelgroups)
-- ============================================================

/-- A KEL event parameterized over payload type.
    Events are hash-chained via priorDigest. -/
structure KELEvent (α : Type) where
  sequenceNumber : Nat
  priorDigest : Option Digest
  payload : α
  signer : Key
  signature : Signature
  deriving Repr

/-- A KEL is a list of events (newest first). -/
abbrev KEL (α : Type) := List (KELEvent α)

-- ============================================================
-- KERI event types
-- ============================================================

/-- Witness configuration change. -/
structure WitnessConfig where
  added : List Key
  removed : List Key
  deriving Repr, DecidableEq

/-- KERI-specific event payloads. -/
inductive EventPayload where
  /-- Inception: establish identifier with initial key set. -/
  | Icp (pfx : SAID)
        (signingThreshold : Nat)
        (keys : List Key)
        (nextThreshold : Nat)
        (nextKeys : List Digest)
        (witnessThreshold : Nat)
        (witnesses : List Key)
  /-- Rotation: key rotation with pre-committed next keys. -/
  | Rot (pfx : SAID)
        (signingThreshold : Nat)
        (keys : List Key)
        (nextThreshold : Nat)
        (nextKeys : List Digest)
        (witnessConfig : WitnessConfig)
  /-- Interaction: anchor data without key change. -/
  | Ixn (pfx : SAID)
        (anchors : List Digest)
  /-- Receipt: non-transferable witness receipt. -/
  | Rct (pfx : SAID)
        (receiptedDigest : Digest)
  deriving Repr

/-- Classification of event types. -/
inductive EventType where
  | Icp | Rot | Ixn | Rct
  deriving Repr, DecidableEq

/-- Extract the event type from a payload. -/
def eventType : EventPayload → EventType
  | .Icp .. => .Icp
  | .Rot .. => .Rot
  | .Ixn .. => .Ixn
  | .Rct .. => .Rct

/-- Extract the prefix from any event payload. -/
def eventPrefix : EventPayload → SAID
  | .Icp p .. => p
  | .Rot p .. => p
  | .Ixn p .. => p
  | .Rct p .. => p

/-- A KERI event. -/
abbrev KERIEvent := KELEvent EventPayload

/-- A KERI Event Log. -/
abbrev KERI_KEL := KEL EventPayload

-- ============================================================
-- Theorems
-- ============================================================

/-- Inception events have type Icp. -/
theorem inception_type (p : SAID) (st : Nat) (ks : List Key)
    (nt : Nat) (nks : List Digest) (wt : Nat) (ws : List Key) :
    eventType (.Icp p st ks nt nks wt ws) = .Icp :=
  rfl

/-- Rotation events have type Rot. -/
theorem rotation_type (p : SAID) (st : Nat) (ks : List Key)
    (nt : Nat) (nks : List Digest) (wc : WitnessConfig) :
    eventType (.Rot p st ks nt nks wc) = .Rot :=
  rfl

/-- eventPrefix extracts the same prefix regardless of event type. -/
theorem prefix_consistent_icp (p : SAID) (st : Nat) (ks : List Key)
    (nt : Nat) (nks : List Digest) (wt : Nat) (ws : List Key) :
    eventPrefix (.Icp p st ks nt nks wt ws) = p :=
  rfl

/-- eventPrefix extracts the same prefix for rotation. -/
theorem prefix_consistent_rot (p : SAID) (st : Nat) (ks : List Key)
    (nt : Nat) (nks : List Digest) (wc : WitnessConfig) :
    eventPrefix (.Rot p st ks nt nks wc) = p :=
  rfl

end KERI.Event
