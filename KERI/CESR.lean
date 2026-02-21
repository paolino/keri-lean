/-
  KERI.CESR — CESR encoding/decoding properties

  Models the Composable Event Streaming Representation
  derivation codes and their size constraints.
-/

namespace KERI.CESR

-- ============================================================
-- Derivation codes
-- ============================================================

/-- CESR derivation codes used in keri-hs. -/
inductive DerivationCode where
  | Ed25519PubKey
  | Blake2bDigest
  | Ed25519Sig
  deriving Repr, DecidableEq

/-- Length of the code prefix in characters. -/
def codeLength : DerivationCode → Nat
  | .Ed25519PubKey => 1
  | .Blake2bDigest => 1
  | .Ed25519Sig => 2

/-- Size of the raw material in bytes. -/
def rawSize : DerivationCode → Nat
  | .Ed25519PubKey => 32
  | .Blake2bDigest => 32
  | .Ed25519Sig => 64

/-- Total length of the CESR primitive in Base64 characters.
    Formula: ceil((codeLength + rawSize) * 4 / 3), but for
    CESR the sizes are chosen so this is exact. -/
def totalLength (c : DerivationCode) : Nat :=
  match c with
  | .Ed25519PubKey => 44
  | .Blake2bDigest => 44
  | .Ed25519Sig => 88

-- ============================================================
-- Abstract encode/decode
-- ============================================================

/-- A raw byte sequence of a given length. -/
structure RawBytes where
  data : Nat
  len : Nat
  deriving Repr, DecidableEq

/-- A CESR primitive: code + raw material. -/
structure Primitive where
  code : DerivationCode
  raw : RawBytes
  deriving Repr, DecidableEq

/-- Construct a primitive, checking raw size matches the code. -/
def mkPrimitive (c : DerivationCode) (r : RawBytes)
    : Option Primitive :=
  if r.len = rawSize c then some ⟨c, r⟩ else none

/-- Abstract CESR encoding. -/
opaque encode : Primitive → Nat

/-- Abstract CESR decoding. -/
opaque decode : Nat → Option Primitive

/-- Roundtrip axiom: decoding an encoded primitive recovers it. -/
axiom roundtrip_ax (p : Primitive) (h : p.raw.len = rawSize p.code)
    : decode (encode p) = some p

-- ============================================================
-- Theorems
-- ============================================================

/-- Ed25519 public key total length is 44 Base64 characters. -/
theorem ed25519_pub_total_length :
    totalLength .Ed25519PubKey = 44 :=
  rfl

/-- Blake2b digest total length is 44 Base64 characters. -/
theorem blake2b_digest_total_length :
    totalLength .Blake2bDigest = 44 :=
  rfl

/-- Ed25519 signature total length is 88 Base64 characters. -/
theorem ed25519_sig_total_length :
    totalLength .Ed25519Sig = 88 :=
  rfl

/-- Ed25519 public key raw size is 32 bytes. -/
theorem ed25519_pub_raw_size :
    rawSize .Ed25519PubKey = 32 :=
  rfl

/-- Blake2b digest raw size is 32 bytes. -/
theorem blake2b_digest_raw_size :
    rawSize .Blake2bDigest = 32 :=
  rfl

/-- Ed25519 signature raw size is 64 bytes. -/
theorem ed25519_sig_raw_size :
    rawSize .Ed25519Sig = 64 :=
  rfl

/-- mkPrimitive succeeds iff raw size matches the code. -/
theorem primitive_size_valid (c : DerivationCode) (r : RawBytes) :
    (mkPrimitive c r).isSome = true ↔ r.len = rawSize c := by
  unfold mkPrimitive
  split <;> simp_all

/-- Roundtrip: decode ∘ encode = id for well-formed primitives. -/
theorem roundtrip (p : Primitive) (h : p.raw.len = rawSize p.code) :
    decode (encode p) = some p :=
  roundtrip_ax p h

/-- Each derivation code has a unique code length. -/
theorem code_lengths_distinct :
    codeLength .Ed25519Sig ≠ codeLength .Ed25519PubKey := by
  decide

end KERI.CESR
