import Proofs.Runtime.SchnorrAGMExecution

/-! The scalar projection used by the DLog solver. Reading returns the actual
cache entry, so extraction need not repeat a lookup. The verification Boolean
is discarded by the original solver; the joint scalar/state law below proves
that omitting its pure computation preserves that solver exactly. -/

open OracleComp OracleSpec AlgebraicGroupModel.Interaction Schnorr.AGM

namespace Signatures.Runtime.SchnorrAGM

variable {F G M : Type} [Field F] [DecidableEq F] [DecidableEq G] [DecidableEq M]
  [SampleableType F]

def readEntry (key : M × G) (a : Affine F) : StateT (State F G M) ProbComp (Reduction.Entry F) :=
  fun s => match cacheMap s.cache key with
    | some e => pure (e, s)
    | none => do
        let c ← $ᵗ F
        pure (⟨c, some a⟩, record s key a c)

def entrySolution (z : F) (entry : Reduction.Entry F) : F :=
  match entry.representation with
  | some a => (z - a.constant) / (a.secret + entry.challenge)
  | none => 0

def finishScalar (out : Explained F (M × F) (Group G)) : StateT (State F G M) ProbComp F := do
  match out.value.groups (), out.coefficients () with
  | [R], [coeff] =>
      let s ← get
      let e ← readEntry (out.value.data.1, R) (flatten coeff s.representations)
      pure (entrySolution out.value.data.2 e)
  | _, _ => pure 0

theorem readEntry_challenge (key : M × G) (a : Affine F) (s : State F G M) :
    (fun p => (p.1.challenge, p.2)) <$> (readEntry key a).run s = (read key a).run s := by
  cases hc : cacheMap s.cache key <;>
    simp [readEntry, read, StateT.run, hc, bind_pure_comp, Functor.map_map]

theorem readEntry_cached (key : M × G) (a : Affine F) (s : State F G M)
    (p : Reduction.Entry F × State F G M) (hp : p ∈ support ((readEntry key a).run s)) :
    cacheMap p.2.cache key = some p.1 := by
  cases hc : cacheMap s.cache key with
  | some e =>
      have he : p = (e, s) := by simpa [readEntry, StateT.run, hc] using hp
      subst p
      exact hc
  | none =>
      simp only [readEntry, StateT.run, hc, bind_pure_comp, support_map, Set.mem_image] at hp
      obtain ⟨c, _, rfl⟩ := hp
      simp [record, cacheMap]

variable [AddCommGroup G] [Module F G]

theorem finishScalar_eq (g pk : G) (out : Explained F (M × F) (Group G)) (s : State F G M) :
    (finishScalar out).run s = (fun p => (p.1.2, p.2)) <$> (finish g pk out).run s := by
  rcases out with ⟨⟨⟨m, z⟩, groups⟩, rows⟩
  cases hg : groups () with
  | nil => simp [finishScalar, finish, hg, StateT.run_pure]
  | cons R gs =>
      cases gs with
      | cons R' gs => simp [finishScalar, finish, hg, StateT.run_pure]
      | nil =>
          cases hr : rows () with
          | nil => simp [finishScalar, finish, hg, hr, StateT.run_pure]
          | cons coeff cs =>
              cases cs with
              | cons coeff' cs => simp [finishScalar, finish, hg, hr, StateT.run_pure]
              | nil =>
                  simp only [finishScalar, finish, hg, hr, StateT.run_bind, StateT.run_get,
                    StateT.run_map, pure_bind, bind_pure_comp, map_bind, Functor.map_map]
                  cases hc : cacheMap s.cache (m, R) with
                  | some e =>
                      cases e with | mk c a =>
                        cases a <;> simp [readEntry, read, hc, entrySolution, StateT.run]
                  | none =>
                      simp [readEntry, read, hc, entrySolution, StateT.run,
                        bind_pure_comp, Functor.map_map, record, cacheMap]

/-- The optimized terminal is the original named finite-list DLog solver. -/
theorem dlogReduction_finishScalar (adv : Adversary F G M) (g pk : G) :
    dlogReduction adv g pk =
      (fun p => p.1) <$> ((do
        let out ← simulateQ (handler g pk) (adv.main (initial g pk))
        finishScalar out).run ({} : State F G M)) := by
  simp only [dlogReduction, run, StateT.run_bind, map_bind]
  congr 1
  funext p
  rw [finishScalar_eq g pk]
  simp only [Functor.map_map]

end Signatures.Runtime.SchnorrAGM
