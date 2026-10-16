import Signatures.Runtime.Cache
import Signatures.BLS.Spec.ROMInternal
import VCVio.OracleComp.QueryTracking.RandomOracle.Basic

/-! Exact representation bridges for the compiled cache. `cacheMap` is a proof-level
abstraction of the association list, not a constant-time operation available to programs.
The implementation continues to execute and pay for the full list scan. -/

open OracleComp OracleSpec

namespace Signatures.Runtime

def cacheMap {K V : Type} [DecidableEq K] : List (K × V) → K → Option V
  | [], _ => none
  | (k, v) :: xs, q => if k = q then some v else cacheMap xs q

theorem cacheMap_cons {K V : Type} [DecidableEq K] (k : K) (v : V) (xs : List (K × V)) :
    cacheMap ((k, v) :: xs) = Function.update (cacheMap xs) k (some v) := by
  funext q
  by_cases h : k = q
  · subst q; simp [cacheMap]
  · simp [cacheMap, h, Ne.symm h]

theorem lookupValue_cacheMap {K V : Type} [DecidableEq K]
    (k : K) (default : V) (xs : List (K × V)) :
    lookupValue k default xs =
      match cacheMap xs k with
      | none => (false, default)
      | some v => (true, v) := by
  induction xs with
  | nil => rfl
  | cons p xs ih =>
      rcases p with ⟨k', v⟩
      by_cases h : k' = k <;> simp [lookupValue, cacheMap, h, ih]

variable {Atom : Type} {base : Atom → Type} {Op Cmd : Ty Atom → Ty Atom → Type}
  {key val : Ty Atom} {I : Type} {spec : OracleSpec I}

theorem lookup_getD (P : Primitives base Op) (eq : Op (.pair key key) .bool)
    [DecidableEq (key.Value base)]
    (heq : ∀ x y, P.execute eq (x, y) = decide (x = y))
    (k : key.Value base) (default : val.Value base) (xs : List (key.Value base × val.Value base)) :
    ((lookup eq).run P (k, default, xs, ())).value.2 = (cacheMap xs k).getD default := by
  rw [lookup_correct P eq heq, lookupValue_cacheMap]
  cases cacheMap xs k <;> rfl

theorem cacheHandler_map (P : Primitives base Op) (H : Handler base Cmd spec)
    (eq : Op (.pair key key) .bool) (draw : Cmd .unit val)
    [DecidableEq (key.Value base)]
    (heq : ∀ x y, P.execute eq (x, y) = decide (x = y))
    (k : key.Value base) (default : val.Value base) (xs : List (key.Value base × val.Value base)) :
    (fun z => (z.1.value, cacheMap z.2)) <$> (cacheHandler P H eq draw default k).run xs =
      match cacheMap xs k with
      | some v => pure (v, cacheMap xs)
      | none => (fun r => (r.value, Function.update (cacheMap xs) k (some r.value))) <$> H draw () := by
  have h := congrArg (Functor.map (fun p : val.Value base × List (key.Value base × val.Value base) =>
    (p.1, cacheMap p.2))) (cacheHandler_erase P H eq draw heq k default xs)
  cases hc : cacheMap xs k <;>
    simpa [lookupValue_cacheMap, hc, cacheMap_cons] using h

/-- The list implementation refines the very same lazy scalar cache used in the BLS game.
The signing set is unchanged by this access. No sampling occurs on a cache hit. -/
theorem cacheHandler_getDlogS (P : Primitives base Op) (H : Handler base Cmd unifSpec)
    (eq : Op (.pair key key) .bool) (draw : Cmd .unit val)
    [DecidableEq (key.Value base)] [SampleableType (val.Value base)]
    (heq : ∀ x y, P.execute eq (x, y) = decide (x = y))
    (hdraw : Run.value <$> H draw () = ($ᵗ (val.Value base) : ProbComp (val.Value base)))
    (k : key.Value base) (default : val.Value base) (xs : List (key.Value base × val.Value base))
    (signed : Finset (key.Value base)) :
    (fun z => (z.1.value, (cacheMap z.2, signed))) <$>
        (cacheHandler P H eq draw default k).run xs =
      (BLS.ROM.Internal.getDlogS (F := val.Value base) k).run (cacheMap xs, signed) := by
  have h := congrArg (Functor.map (fun p : val.Value base × (key.Value base → Option (val.Value base)) =>
    (p.1, (p.2, signed)))) (cacheHandler_map P H eq draw heq k default xs)
  cases hc : cacheMap xs k with
  | some v => simpa [hc, BLS.ROM.Internal.getDlogS] using h
  | none =>
      simpa [hc, BLS.ROM.Internal.getDlogS, bind_pure_comp, ← hdraw] using h

/-- The coin-cache representation is VCVio's `QueryCache`, not an eager sampled table. -/
def listQueryCache {K V : Type} [DecidableEq K] (xs : List (K × V)) : (K →ₒ V).QueryCache :=
  .ofFn (cacheMap xs)

theorem listQueryCache_cons {K V : Type} [DecidableEq K] (k : K) (v : V) (xs : List (K × V)) :
    listQueryCache ((k, v) :: xs) = (listQueryCache xs).cacheQuery k v := by
  apply QueryCache.ext
  intro q
  by_cases h : k = q
  · subst q; simp [listQueryCache, cacheMap]
  · simp [listQueryCache, cacheMap, h, Ne.symm h]

theorem cacheHandler_randomOracle (P : Primitives base Op) (H : Handler base Cmd unifSpec)
    (eq : Op (.pair key key) .bool) (draw : Cmd .unit val)
    [DecidableEq (key.Value base)] [SampleableType (val.Value base)]
    (heq : ∀ x y, P.execute eq (x, y) = decide (x = y))
    (hdraw : Run.value <$> H draw () = ($ᵗ (val.Value base) : ProbComp (val.Value base)))
    (k : key.Value base) (default : val.Value base) (xs : List (key.Value base × val.Value base)) :
    (fun z => (z.1.value, listQueryCache z.2)) <$> (cacheHandler P H eq draw default k).run xs =
      ((key.Value base →ₒ val.Value base).randomOracle k).run (listQueryCache xs) := by
  have h := congrArg (Functor.map (fun p : val.Value base × List (key.Value base × val.Value base) =>
    (p.1, listQueryCache p.2))) (cacheHandler_erase P H eq draw heq k default xs)
  have hu (v : val.Value base) :
      QueryCache.ofFn (cacheMap ((k, v) :: xs)) =
        (QueryCache.ofFn (cacheMap xs) : (key.Value base →ₒ val.Value base).QueryCache).cacheQuery k v :=
    listQueryCache_cons k v xs
  rw [randomOracle.run_eq]
  simp only [listQueryCache, QueryCache.ofFn_apply]
  cases hc : cacheMap xs k with
  | some v => simpa [lookupValue_cacheMap, hc, listQueryCache] using h
  | none =>
      simpa [lookupValue_cacheMap, hc, bind_pure_comp,
        listQueryCache, hu, ← hdraw] using h

end Signatures.Runtime
