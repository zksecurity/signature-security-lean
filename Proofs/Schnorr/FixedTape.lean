import VCVio.CryptoFoundations.SeededFork
import ToMathlib.MeasureTheory.MeasurableSpace.Option

/-!
Fixed-private-tape replay for Schnorr's simulated adversary. Uniform draws and
fresh hash challenges are different oracle families. The seed covers every
private draw on every reply path, including private draws after the fork.

These are replay infrastructure lemmas. `FixedTapeROM` separately supplies a
fixed-tape EUF-CMA probability theorem with explicit seed-coverage premises.
The existing compiled contextual replay endpoint does not yet use this construction.
-/

open OracleComp OracleSpec

namespace Schnorr.FixedTape

abbrev Spec (F : Type) := unifSpec + (Unit →ₒ F)

/-- `qR` bounds each supported private sampling family; `qH` counts fresh challenges. -/
def bounds (randomBound qR qH : Nat) : Nat ⊕ Unit → Nat
  | .inl n => if n ≤ randomBound then qR else 0
  | .inr () => qH

-- Expose the challenge bound when Lean compares dependent `Fin` instances.
attribute [local implicit_reducible] bounds

/-- Every potentially used family is seeded, not only the challenge family. -/
def families (randomBound : Nat) : List (Nat ⊕ Unit) :=
  (List.range (randomBound + 1)).map Sum.inl ++ [Sum.inr ()]

theorem families_cover (randomBound qR qH : Nat) (i : Nat ⊕ Unit)
    (hi : bounds randomBound qR qH i ≠ 0) : i ∈ families randomBound := by
  cases i with
  | inl n =>
      have hn : n ≤ randomBound := by
        by_contra hn
        exact hi (by simp [bounds, hn])
      simp [families, hn]
  | inr u => cases u; simp [families]

variable {F A : Type} [SampleableType F]

/-- Bellare--Neven replay with all bounded private families seeded before either run.
`cf` has the upstream lemma's `qH + 1` slots. The application must show that its
selected slot really occurs; the probability lemma alone is not an extraction proof. -/
def fork [DecidableEq F] (main : OracleComp (Spec F) A) (randomBound qR qH : Nat)
    (cf : A → Option (Fin (qH + 1))) : OracleComp (Spec F) (Option (A × A)) :=
  seededFork main (bounds randomBound qR qH) (families randomBound) (.inr ()) cf

noncomputable local instance [Fintype F] [Inhabited F] : IsUniformSpec (Unit →ₒ F) :=
  IsUniformSpec.ofFintypeInhabited _

/-- The seeded fork has the established quadratic success bound. Seed coverage
and Schnorr transcript extraction are separate obligations, not hidden premises. -/
theorem fork_success_bound [DecidableEq F] [Fintype F] [Inhabited F]
    [MeasurableSpace A] [DiscreteMeasurableSpace A]
    (main : OracleComp (Spec F) A) (randomBound qR qH : Nat)
    (cf : A → Option (Fin (qH + 1))) :
    let acc : ENNReal := ∑ s, 𝒟[cf <$> main] {some s}
    acc * (acc / (qH + 1 : ENNReal) - (Fintype.card F : ENNReal)⁻¹) ≤
      𝒟[fork main randomBound qR qH cf] {r | r.isSome} := by
  rw [evalDist_apply _ Option.measurableSet_isSome]
  have hcard : Fintype.card ((Spec F).Range (.inr ())) = Fintype.card F :=
    Fintype.card_congr (Equiv.refl F)
  simpa only [fork, bounds, evalDist_apply_singleton, hcard, Nat.cast_add,
    Nat.cast_one, Set.mem_ofPred_eq] using
    le_probEvent_isSome_seededFork main (bounds randomBound qR qH)
      (families randomBound) (.inr ()) cf

/-- A generated seed has enough entries even for private draws not used in the first run. -/
theorem seed_covers (randomBound qR qH : Nat) (seed : QuerySeed (Spec F))
    (hs : seed ∈ support (generateSeed (Spec F)
      (bounds randomBound qR qH) (families randomBound))) :
    ∀ i, bounds randomBound qR qH i ≤ (seed i).length := by
  intro i
  exact le_length_of_mem_support_generateSeed_of_covers
    (Spec F) (bounds randomBound qR qH) (families randomBound) seed i hs
    (fun j hj => families_cover randomBound qR qH j (Nat.ne_of_gt hj))

omit [SampleableType F] in
/-- Replacing a hash challenge preserves the entire private tape, not just its prefix. -/
theorem private_seed_unchanged (seed : QuerySeed (Spec F)) (slot n : Nat) (c : F) :
    ((seed.takeAtIndex (.inr ()) slot).addValue (.inr ()) c) (.inl n) =
      seed (.inl n) := by
  simp [QuerySeed.addValue, QuerySeed.addValues]

/-- The first execution uses no live draws once the complete seed is installed. -/
theorem first_no_live (main : OracleComp (Spec F) A) (randomBound qR qH : Nat)
    (hmain : IsPerIndexQueryBound main (bounds randomBound qR qH))
    (seed : QuerySeed (Spec F))
    (hs : seed ∈ support (generateSeed (Spec F)
      (bounds randomBound qR qH) (families randomBound))) :
    IsPerIndexQueryBound ((simulateQ seededOracle main).run' seed) 0 :=
  seededOracle.isPerIndexQueryBound_run'_zero hmain
    (seed_covers randomBound qR qH seed hs)

/-- Only hash challenges may be sampled live in the replay; private randomness is fixed. -/
theorem replay_live_bound (main : OracleComp (Spec F) A) (randomBound qR qH : Nat)
    (hmain : IsPerIndexQueryBound main (bounds randomBound qR qH))
    (seed : QuerySeed (Spec F))
    (hs : seed ∈ support (generateSeed (Spec F)
      (bounds randomBound qR qH) (families randomBound)))
    (slot : Fin (qH + 1)) (c : F) :
    IsPerIndexQueryBound
      ((simulateQ seededOracle main).run'
        ((seed.takeAtIndex (.inr ()) slot.val).addValue (.inr ()) c))
      (Function.update 0 (.inr ()) (qH - (slot.val + 1))) :=
  seededOracle.isPerIndexQueryBound_run'_takeAtIndex_addValue (i := Sum.inr ()) hmain
    (seed_covers randomBound qR qH seed hs) slot c

end Schnorr.FixedTape
