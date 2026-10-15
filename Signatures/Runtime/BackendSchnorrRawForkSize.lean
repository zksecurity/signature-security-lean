import Signatures.Runtime.BackendSchnorrRawFork

/-! Controller frame invariants. The pass's own validity predicates are kept
alongside encoded widths and the two tape capacities. Product bounds count
every occurrence, including configurations and first outputs retained for replay. -/

open PFunctor

namespace Signatures.Runtime.Schnorr.RawTape.NativeFork

open BackendProgram

def Both {A B : Type} (preLeft : A → Prop) (preRight : B → Prop) (p : A × B) : Prop :=
  preLeft p.1 ∧ preRight p.2

universe v w

variable {C : StepClass.{0, v}} [C.HasProd]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {F G₁ G₂ K M : Type}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))

def Ready {ty : Ty CryptoAtom} (width : Nat)
    (valid : ty.Value (cryptoBase F G₁ G₂ K M) → Prop)
    (x : ty.Value (cryptoBase F G₁ G₂ K M)) : Prop :=
  valid x ∧ Q.size (rep.ty ty) x ≤ width

def Incoming {config : Ty CryptoAtom} (width savedCap remainingCap : Nat)
    (valid : config.Value (cryptoBase F G₁ G₂ K M) → Prop) :
    (passInput config).Value (cryptoBase F G₁ G₂ K M) → Prop :=
  Both (NativeUniform.StateBound (Q := Q) rep width savedCap remainingCap) (Ready (Q := Q) rep width valid)

def Returned {out : Ty CryptoAtom} (width savedCap remainingCap : Nat)
    (valid : out.Value (cryptoBase F G₁ G₂ K M) → Prop) :
    (passOutput out).Value (cryptoBase F G₁ G₂ K M) → Prop :=
  Both (Ready (Q := Q) rep width valid) (NativeUniform.StateBound (Q := Q) rep width savedCap remainingCap)

def Result {out : Ty CryptoAtom} (width : Nat)
    (valid : out.Value (cryptoBase F G₁ G₂ K M) → Prop) :
    Unit ⊕ (out.Value (cryptoBase F G₁ G₂ K M) × out.Value (cryptoBase F G₁ G₂ K M)) → Prop :=
  Sum.elim (fun _ => True) (Both (Ready (Q := Q) rep width valid) (Ready (Q := Q) rep width valid))

def frameWidth (width firstCap secondCap : Nat) : Nat :=
  (16 * (firstCap + secondCap) + 64) * width

variable [C.HasSum] [C.HasOption]
  {header : Nat} (sizes : SizeLaws Q header)

include sizes

theorem both_size {A B : Type} (a : C.Str A) (b : C.Str B) (P : A → Prop) (R : B → Prop)
    (width leftCap rightCap : Nat) (hh : header ≤ width)
    (hl : ∀ x, P x → Q.size a x ≤ leftCap * width)
    (hr : ∀ x, R x → Q.size b x ≤ rightCap * width) :
    ∀ x, Both P R x → Q.size (StepClass.HasProd.prod a b) x ≤ (leftCap + rightCap + 1) * width := by
  intro x hx
  have h₁ := hl x.1 hx.1
  have h₂ := hr x.2 hx.2
  have hp := sizes.prod_le a b x
  nlinarith

theorem either_size {A B : Type} (a : C.Str A) (b : C.Str B) (P : A → Prop) (R : B → Prop)
    (width cap : Nat) (hh : header ≤ width)
    (hl : ∀ x, P x → Q.size a x ≤ cap * width)
    (hr : ∀ x, R x → Q.size b x ≤ cap * width) :
    ∀ x, Sum.elim P R x → Q.size (StepClass.HasSum.sum a b) x ≤ (cap + 1) * width := by
  intro x hx
  have hs := sizes.sum_le a b x
  cases x with
  | inl x => have h := hl x hx; dsimp only [Sum.elim] at hs; nlinarith
  | inr x => have h := hr x hx; dsimp only [Sum.elim] at hs; nlinarith

/-- An invariant together with its proved encoded footprint, in units of the
base width. Products charge both occurrences of retained values. -/
structure Frame {A : Type} (a : C.Str A) (width : Nat) where
  property : A → Prop
  factor : Nat
  size_le : ∀ x, property x → Q.size a x ≤ factor * width

namespace Frame

def pair {A B : Type} {a : C.Str A} {b : C.Str B} {width : Nat}
    (p : Frame (Q := Q) a width) (r : Frame (Q := Q) b width) (hh : header ≤ width) :
    Frame (Q := Q) (StepClass.HasProd.prod a b) width where
  property := Both p.property r.property
  factor := p.factor + r.factor + 1
  size_le := both_size sizes a b p.property r.property width p.factor r.factor hh p.size_le r.size_le

def sum {A B : Type} {a : C.Str A} {b : C.Str B} {width : Nat}
    (p : Frame (Q := Q) a width) (r : Frame (Q := Q) b width) (hh : header ≤ width) :
    Frame (Q := Q) (StepClass.HasSum.sum a b) width where
  property := Sum.elim p.property r.property
  factor := p.factor + r.factor + 1
  size_le := by
    intro x hx
    have hs := sizes.sum_le a b x
    cases x with
    | inl x => have h := p.size_le x hx; dsimp only [Sum.elim] at hs; nlinarith
    | inr x => have h := r.size_le x hx; dsimp only [Sum.elim] at hs; nlinarith

omit sizes in
def ready (ty : Ty CryptoAtom) (width : Nat)
    (valid : ty.Value (cryptoBase F G₁ G₂ K M) → Prop) :
    Frame (Q := Q) (rep.ty ty) width where
  property := Ready (Q := Q) rep width valid
  factor := 1
  size_le := fun _ h => by simpa using h.2

def state (lists : ListSizeLaws Q rep.data header) (width savedCap remainingCap : Nat)
    (hh : header ≤ width) : Frame (Q := Q) (rep.ty stateTy) width where
  property := NativeUniform.StateBound (Q := Q) rep width savedCap remainingCap
  factor := 6 * (savedCap + remainingCap) + 3
  size_le := NativeUniform.state_size rep sizes lists width savedCap remainingCap hh

end Frame

end Signatures.Runtime.Schnorr.RawTape.NativeFork
