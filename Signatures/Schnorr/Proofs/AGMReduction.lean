import Signatures.Schnorr.Proofs.AGMRepresentation

/-! A single-pass AGM reduction. The first fresh hash request records its affine
representation before drawing its challenge; repeated requests retain that record.
Signing replies extend the received representation list in chronological order.
The adaptive probability comparison is a separate proof obligation. -/

open OracleComp OracleSpec AlgebraicGroupModel.Interaction

namespace Schnorr.AGM.Reduction

variable {F G M : Type} [Field F] [AddCommGroup G] [Module F G]

/-- `none` marks a simulator-programmed signing entry. -/
structure Entry (F : Type) where
  challenge : F
  representation : Option (Affine F)

structure State (F G M : Type) [Field F] where
  representations : List (Affine F) := initialRepresentations
  cache : M × G → Option (Entry F) := fun _ => none
  signed : List M := []
  malformed : Bool := false
  bad : Bool := false

/-- Cached live hashes retain the point's representation and, until bad, an
invertible extraction denominator. Programmed entries belong to signed messages. -/
def State.Valid (g pk : G) (s : State F G M) : Prop :=
  ∀ key e, s.cache key = some e →
    match e.representation with
    | none => key.1 ∈ s.signed
    | some a => a.eval g pk = key.2 ∧ (s.bad = false → a.secret + e.challenge ≠ 0)

theorem initial_valid (g pk : G) : ({} : State F G M).Valid g pk := by
  intro key e h
  cases h

variable [DecidableEq F] [DecidableEq G] [DecidableEq M]

/-- Used only for a fresh point. The representation is already fixed when c is drawn. -/
def record (s : State F G M) (key : M × G) (a : Affine F) (c : F) : State F G M :=
  { s with cache := Function.update s.cache key (some ⟨c, some a⟩)
           bad := s.bad || decide (a.secret + c = 0) }

theorem record_valid (g pk : G) (s : State F G M) (hs : s.Valid g pk)
    (key : M × G) (a : Affine F) (ha : a.eval g pk = key.2) (c : F) :
    (record s key a c).Valid g pk := by
  intro key' e he
  by_cases hk : key' = key
  · subst key'
    simp [record] at he
    subst e
    refine ⟨ha, ?_⟩
    simp [record]
  · have he' : s.cache key' = some e := by simpa [record, hk] using he
    have h := hs key' e he'
    cases hr : e.representation with
    | none => simpa only [hr, record] using h
    | some a' =>
        simp only [hr] at h ⊢
        refine ⟨h.1, fun hb => h.2 ?_⟩
        simpa [record] using (Bool.or_eq_false_iff.mp hb).1

/-- Signing collisions keep the previous entry, exactly as the managed FS simulator. -/
def signedState (s : State F G M) (g pk : G) (m : M) (c z : F) : State F G M :=
  let R := z • g - c • pk
  { s with
      representations := s.representations ++ [signingRepresentation c z]
      signed := s.signed ++ [m]
      cache := match s.cache (m, R) with
        | some _ => s.cache
        | none => Function.update s.cache (m, R) (some ⟨c, none⟩) }

omit [DecidableEq F] in
theorem signedState_valid (g pk : G) (s : State F G M) (hs : s.Valid g pk)
    (m : M) (c z : F) : (signedState s g pk m c z).Valid g pk := by
  intro key e he
  by_cases hc : s.cache (m, z • g - c • pk) = none
  · by_cases hk : key = (m, z • g - c • pk)
    · subst key
      simp [signedState, hc] at he
      subst e
      simp [signedState]
    · have he' : s.cache key = some e := by simpa [signedState, hc, hk] using he
      have h := hs key e he'
      cases hr : e.representation with
      | none => simp only [hr] at h ⊢; exact List.mem_append_left _ h
      | some a => simpa only [hr, signedState] using h
  · cases hcache : s.cache (m, z • g - c • pk) with
    | none => exact (hc hcache).elim
    | some old =>
        have he' : s.cache key = some e := by simpa [signedState, hcache] using he
        have h := hs key e he'
        cases hr : e.representation with
        | none => simp only [hr] at h ⊢; exact List.mem_append_left _ h
        | some a => simpa only [hr, signedState] using h

omit [DecidableEq F] in
theorem signedState_basis (g pk : G) (s : State F G M) (m : M) (c z : F) :
    representedBasis g pk (signedState s g pk m c z).representations =
      extend (representedBasis g pk s.representations)
        (signingReply (z • g - c • pk) z).groups := by
  funext t
  simp [signedState, representedBasis, extend, signingReply, signingRepresentation_eval]

variable [SampleableType F]

def read (key : M × G) (a : Affine F) : StateT (State F G M) ProbComp F :=
  fun s => match s.cache key with
    | some e => pure (e.challenge, s)
    | none => do
        let c ← $ᵗ F
        pure (c, record s key a c)

def rejected (s : State F G M) : State F G M := { s with malformed := true }

omit [DecidableEq F] [DecidableEq G] [DecidableEq M] [SampleableType F] in
theorem rejected_valid (g pk : G) (s : State F G M) (hs : s.Valid g pk) :
    (rejected s).Valid g pk := hs

def handler (g pk : G) :
    QueryImpl (explainedSpec F (Group G) (Request M) (Reply F M))
      (StateT (State F G M) ProbComp) := by
  intro ⟨⟨request, groups⟩, coefficients⟩
  cases request with
  | random n => exact fun s => do
      let v ← unifSpec.query n
      pure (⟨v, fun _ => []⟩, if groups () = [] then s else rejected s)
  | hash m => exact fun s =>
      match groups (), coefficients () with
      | [R], [coeff] => do
          let (c, t) ← (read (m, R) (flatten coeff s.representations)).run s
          pure (scalarReply c, t)
      | _, _ => pure (scalarReply (0 : F), rejected s)
  | sign m => exact fun s =>
      if groups () ≠ [] then pure (scalarReply (0 : F), rejected s)
      else
        do
        let c ← $ᵗ F
        let z ← $ᵗ F
        pure (signingReply (z • g - c • pk) z, signedState s g pk m c z)

/-- The success flag is retained for the probability comparison; extraction uses
the first cached representation, never a new coefficient chosen after hashing. -/
def finish (g pk : G) (out : Explained F (M × F) (Group G)) :
    StateT (State F G M) ProbComp (Bool × F) := do
  match out.value.groups (), out.coefficients () with
  | [R], [coeff] =>
      let (m, z) := out.value.data
      let s ← get
      let c ← read (m, R) (flatten coeff s.representations)
      let s ← get
      let accepted := !s.malformed && decide (m ∉ s.signed ∧ z • g = R + c • pk)
      let solution := match s.cache (m, R) with
        | some ⟨_, some a⟩ => (z - a.constant) / (a.secret + c)
        | _ => 0
      pure (accepted, solution)
  | _, _ => pure (false, 0)

def run (g pk : G) (adv : Adversary F G M) : ProbComp ((Bool × F) × State F G M) :=
  (do
    let out ← simulateQ (handler g pk) (adv.main (initial g pk))
    finish g pk out).run {}

def dlogReduction (g : G) (adv : Adversary F G M) : DiffieHellman.DLogAdversary F G :=
  fun _ pk => (fun result => result.1.2) <$> run g pk adv

end Schnorr.AGM.Reduction
