/-
  KERI.KEL — Hash chain and log integrity invariants

  Defines hash chain validity for generic KELs (extracted
  from kelgroups) and KERI-specific replay properties.
-/
import KERI.Crypto
import KERI.Event
import KERI.KeyState

namespace KERI.KEL

open KERI.Crypto
open KERI.Event
open KERI.KeyState

-- ============================================================
-- Hash chain validity (extracted from kelgroups)
-- ============================================================

/-- Hash chain validity: sequence numbers are consecutive and
    non-inception events have prior digests.
    KEL is stored newest-first. -/
def hashChainValid {α : Type} (kel : KEL α) : Prop :=
  match kel with
  | [] => True
  | [e] => e.sequenceNumber = 0 ∧ e.priorDigest = none
  | e :: rest =>
    e.priorDigest.isSome
    ∧ (match rest.head? with
       | some prev => e.sequenceNumber = prev.sequenceNumber + 1
       | none => False)
    ∧ hashChainValid rest

-- ============================================================
-- Theorems
-- ============================================================

/-- Empty KEL has a trivially valid hash chain. -/
theorem empty_chain_valid {α : Type} :
    hashChainValid (α := α) [] :=
  trivial

/-- A single inception event forms a valid hash chain. -/
theorem singleton_chain_valid {α : Type} (e : KELEvent α)
    (hseq : e.sequenceNumber = 0)
    (hpd : e.priorDigest = none) :
    hashChainValid [e] :=
  ⟨hseq, hpd⟩

/-- First event in a valid non-empty KEL (the oldest, i.e. last
    in the list) has sequence number 0 and no prior digest. -/
theorem kel_starts_with_inception {α : Type} (kel : KEL α)
    (hne : kel ≠ [])
    (hvalid : hashChainValid kel) :
    ∃ e ∈ kel, e.sequenceNumber = 0 ∧ e.priorDigest = none := by
  induction kel with
  | nil => contradiction
  | cons x xs ih =>
    match xs, hvalid with
    | [], ⟨hseq, hpd⟩ =>
      exact ⟨x, by simp, hseq, hpd⟩
    | _ :: _, ⟨_, _, hrest⟩ =>
      obtain ⟨e, he, hseq, hpd⟩ := ih (by simp) hrest
      exact ⟨e, by simp [he], hseq, hpd⟩

-- ============================================================
-- KEL replay
-- ============================================================

/-- Replay a KEL (oldest-first) to compute the final key state. -/
def replay (events : List KERIEvent) : Option KeyState :=
  match events with
  | [] => none
  | e :: rest =>
    match initialState e with
    | none => none
    | some ks₀ => rest.foldlM (fun ks ev => applyEvent ks ev) ks₀

/-- Replay of an empty event list fails. -/
theorem replay_empty_fails :
    replay [] = none :=
  rfl

/-- Replay of a single valid inception gives the initial state. -/
theorem replay_inception_gives_initial (e : KERIEvent)
    (ks : KeyState)
    (h : initialState e = some ks) :
    replay [e] = some ks := by
  simp [replay, h]

-- ============================================================
-- Signature threshold
-- ============================================================

/-- Count of valid signatures meets a threshold. -/
def thresholdMet (validCount : Nat) (threshold : Nat) : Prop :=
  validCount ≥ threshold

/-- A threshold of 0 is always met. -/
theorem threshold_zero_met (n : Nat) :
    thresholdMet n 0 :=
  Nat.zero_le n

end KERI.KEL
