import Proofs.Runtime.CacheRefinement
import Proofs.Schnorr.AGMReduction

/-! A finite association-list store for the single-pass Schnorr AGM reduction.
Only encountered message/commitment pairs are stored. `erase` is a proof-level
abstraction, not a machine operation. Repeated hashes and signing collisions
preserve the first cached challenge and affine representation. -/

open OracleComp OracleSpec AlgebraicGroupModel.Interaction Schnorr.AGM

namespace Signatures.Runtime.SchnorrAGM

variable {F G M : Type} [Field F] [AddCommGroup G] [Module F G]

structure State (F G M : Type) [Field F] where
  representations : List (Affine F) := initialRepresentations
  cache : List ((M × G) × Reduction.Entry F) := []
  signed : List M := []
  malformed : Bool := false
  bad : Bool := false

variable [DecidableEq F] [DecidableEq G] [DecidableEq M]

def erase (s : State F G M) : Reduction.State F G M :=
  { representations := s.representations
    cache := cacheMap s.cache
    signed := s.signed
    malformed := s.malformed
    bad := s.bad }

omit [AddCommGroup G] [Module F G] [DecidableEq F] in
@[simp] theorem erase_initial : erase ({} : State F G M) = {} := rfl

def record (s : State F G M) (key : M × G) (a : Affine F) (c : F) : State F G M :=
  { s with cache := (key, ⟨c, some a⟩) :: s.cache
           bad := s.bad || decide (a.secret + c = 0) }

omit [AddCommGroup G] [Module F G] in
@[simp] theorem erase_record (s : State F G M) (key : M × G) (a : Affine F) (c : F) :
    erase (record s key a c) = Reduction.record (erase s) key a c := by
  simp only [erase, record, Reduction.record, cacheMap_cons]

def signedState (s : State F G M) (g pk : G) (m : M) (c z : F) : State F G M :=
  let R := z • g - c • pk
  { s with
      representations := s.representations ++ [signingRepresentation c z]
      signed := s.signed ++ [m]
      cache := match cacheMap s.cache (m, R) with
        | some _ => s.cache
        | none => ((m, R), ⟨c, none⟩) :: s.cache }

omit [DecidableEq F] in
@[simp] theorem erase_signedState (s : State F G M) (g pk : G) (m : M) (c z : F) :
    erase (signedState s g pk m c z) = Reduction.signedState (erase s) g pk m c z := by
  cases hc : cacheMap s.cache (m, z • g - c • pk) <;>
    simp [erase, signedState, Reduction.signedState, hc, cacheMap_cons]

def rejected (s : State F G M) : State F G M := { s with malformed := true }

omit [AddCommGroup G] [Module F G] [DecidableEq F] in
@[simp] theorem erase_rejected (s : State F G M) :
    erase (rejected s) = Reduction.rejected (erase s) := rfl

variable [SampleableType F]

def read (key : M × G) (a : Affine F) : StateT (State F G M) ProbComp F :=
  fun s => match cacheMap s.cache key with
    | some e => pure (e.challenge, s)
    | none => do
        let c ← $ᵗ F
        pure (c, record s key a c)

omit [AddCommGroup G] [Module F G] in
/-- Exact query-tree equality, including the absence of sampling on a hit. -/
theorem read_erase (key : M × G) (a : Affine F) (s : State F G M) :
    (fun p => (p.1, erase p.2)) <$> (read key a).run s =
      (Reduction.read key a).run (erase s) := by
  cases hc : cacheMap s.cache key <;>
    simp [read, Reduction.read, StateT.run, erase, hc, bind_pure_comp,
      Functor.map_map, record, Reduction.record, cacheMap_cons]

omit [AddCommGroup G] [Module F G] in
/-- A single read adds at most one encountered key. -/
theorem read_growth (key : M × G) (a : Affine F) (s : State F G M)
    (p : F × State F G M) (hp : p ∈ support ((read key a).run s)) :
    p.2.cache.length ≤ s.cache.length + 1 ∧
      p.2.representations = s.representations ∧ p.2.signed = s.signed := by
  cases hc : cacheMap s.cache key with
  | some e =>
      have he : p = (e.challenge, s) := by simpa [read, StateT.run, hc] using hp
      subst p
      exact ⟨Nat.le_succ _, rfl, rfl⟩
  | none =>
      simp only [read, StateT.run, hc, bind_pure_comp, support_map, Set.mem_image] at hp
      obtain ⟨c, _, rfl⟩ := hp
      exact ⟨by simp [record], rfl, rfl⟩

omit [SampleableType F] [DecidableEq F] in
theorem signedState_growth (s : State F G M) (g pk : G) (m : M) (c z : F) :
    (signedState s g pk m c z).cache.length ≤ s.cache.length + 1 ∧
      (signedState s g pk m c z).representations.length = s.representations.length + 1 ∧
      (signedState s g pk m c z).signed.length = s.signed.length + 1 := by
  cases hc : cacheMap s.cache (m, z • g - c • pk) <;> simp [signedState, hc]

end Signatures.Runtime.SchnorrAGM
