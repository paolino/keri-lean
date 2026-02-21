/-
  KERI.KeyState — Key state machine transitions

  Models the KERI key state and the rules for applying
  events to transition between states.
-/
import KERI.Crypto
import KERI.Event

namespace KERI.KeyState

open KERI.Crypto
open KERI.Event

-- ============================================================
-- Key state
-- ============================================================

/-- The key state maintained by processing a KEL. -/
structure KeyState where
  pfx : SAID
  seqNum : Nat
  lastDigest : Digest
  signingThreshold : Nat
  keys : List Key
  nextThreshold : Nat
  nextKeys : List Digest
  witnessThreshold : Nat
  witnesses : List Key
  deriving Repr, DecidableEq

-- ============================================================
-- State initialization
-- ============================================================

/-- Abstract digest computation over an event. -/
opaque eventDigest : KERIEvent → Digest

/-- Create initial state from an inception event. -/
def initialState (e : KERIEvent) : Option KeyState :=
  match e.payload with
  | .Icp p st ks nt nks wt ws =>
    if e.sequenceNumber = 0 ∧ e.priorDigest = none then
      some {
        pfx := p
        seqNum := 0
        lastDigest := eventDigest e
        signingThreshold := st
        keys := ks
        nextThreshold := nt
        nextKeys := nks
        witnessThreshold := wt
        witnesses := ws
      }
    else none
  | _ => none

-- ============================================================
-- Event application
-- ============================================================

/-- Apply an event to the current key state.
    Returns none if the event is invalid for this state. -/
def applyEvent (ks : KeyState) (e : KERIEvent) : Option KeyState :=
  if e.sequenceNumber ≠ ks.seqNum + 1 then none
  else if eventPrefix e.payload ≠ ks.pfx then none
  else
  match e.payload with
  | .Icp .. => none
  | .Rot _ st newKeys nt nks wc =>
    some {
      pfx := ks.pfx
      seqNum := ks.seqNum + 1
      lastDigest := eventDigest e
      signingThreshold := st
      keys := newKeys
      nextThreshold := nt
      nextKeys := nks
      witnessThreshold := ks.witnessThreshold
      witnesses :=
        ks.witnesses.filter (· ∉ wc.removed) ++ wc.added
    }
  | .Ixn _ _ =>
    some {
      ks with
      seqNum := ks.seqNum + 1
      lastDigest := eventDigest e
    }
  | .Rct _ _ =>
    some ks

-- ============================================================
-- Theorems
-- ============================================================

/-- Initial state from a valid inception has sequence number 0. -/
theorem initial_state_seq_zero (e : KERIEvent)
    (ks' : KeyState)
    (h : initialState e = some ks') :
    ks'.seqNum = 0 := by
  unfold initialState at h
  split at h
  · split at h
    · cases h; rfl
    · contradiction
  · contradiction

/-- Initial state preserves the prefix from inception. -/
theorem initial_state_pfx (e : KERIEvent)
    (p : SAID) (st : Nat) (k : List Key) (nt : Nat)
    (nks : List Digest) (wt : Nat) (ws : List Key)
    (hp : e.payload = .Icp p st k nt nks wt ws)
    (ks' : KeyState)
    (h : initialState e = some ks') :
    ks'.pfx = p := by
  simp [initialState, hp] at h
  obtain ⟨_, rfl⟩ := h; rfl

/-- applyEvent rejects inception events on existing state. -/
theorem apply_rejects_inception (ks : KeyState) (e : KERIEvent)
    (p : SAID) (st : Nat) (k : List Key) (nt : Nat)
    (nks : List Digest) (wt : Nat) (ws : List Key)
    (hp : e.payload = .Icp p st k nt nks wt ws) :
    applyEvent ks e = none := by
  simp [applyEvent, hp]

/-- Successful applyEvent requires correct sequence number. -/
theorem apply_checks_sequence (ks : KeyState) (e : KERIEvent)
    (ks' : KeyState) (h : applyEvent ks e = some ks') :
    e.sequenceNumber = ks.seqNum + 1 := by
  unfold applyEvent at h
  split at h <;> simp_all

/-- Successful applyEvent requires matching prefix. -/
theorem apply_checks_pfx (ks : KeyState) (e : KERIEvent)
    (ks' : KeyState) (h : applyEvent ks e = some ks') :
    eventPrefix e.payload = ks.pfx := by
  unfold applyEvent at h
  split at h <;> simp_all

/-- Receipt events don't change key state. -/
theorem receipt_neutral (ks : KeyState) (e : KERIEvent)
    (p : SAID) (d : Digest)
    (hp : e.payload = .Rct p d)
    (hseq : e.sequenceNumber = ks.seqNum + 1)
    (hpfx : p = ks.pfx) :
    applyEvent ks e = some ks := by
  simp [applyEvent, hp, hseq, eventPrefix, hpfx]

end KERI.KeyState
