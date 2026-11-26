import Signatures.Schnorr.Spec.NonzeroNonce
import Mathlib.FieldTheory.Finite.Basic
import VCVio.OracleComp.QueryTracking.RandomOracle.DeferredSampling
import VCVio.OracleComp.Constructions.SampleableType.Measure

/-! Repairing a uniform scalar's zero value with an independent uniform unit
gives exactly a uniform nonzero scalar. A finite bijection proves the law;
the sampler needs no rejection loop or secret-dependent enumeration. -/

open OracleComp OracleSpec

namespace Schnorr.NonzeroNonce

variable {F : Type} [Field F] [DecidableEq F]

/-- Zero consumes the replacement; nonzero values retain the original draw. -/
def repair (r : F) (u : Fˣ) : F := if r = 0 then u else r

def repairEquiv : F × Fˣ ≃ Fˣ × F where
  toFun p := if h : p.1 = 0 then (p.2, 0) else (Units.mk0 p.1 h, p.2)
  invFun p := if h : p.2 = 0 then (0, p.1) else (p.1, Units.mk0 p.2 h)
  left_inv p := by
    rcases p with ⟨r, u⟩
    by_cases h : r = 0
    · simp [h]
    · simp [h, Units.ne_zero u]
  right_inv p := by
    rcases p with ⟨u, r⟩
    by_cases h : r = 0
    · simp [h]
    · simp [h, Units.ne_zero u]

theorem repairEquiv_value (r : F) (u : Fˣ) :
    ((repairEquiv (r, u)).1 : F) = repair r u := by
  by_cases h : r = 0 <;> simp [repairEquiv, repair, h]

variable [SampleableType F] [SampleableType Fˣ] [Finite F]

/-- Equality of the complete sampling laws, including the zero branch. -/
theorem repair_uniform :
    (do let r ← ($ᵗ F); let u ← ($ᵗ Fˣ); pure (repair r u)) =ᵈ ((fun u : Fˣ => (u : F)) <$> ($ᵗ Fˣ)) := by
  have he : (do let r ← ($ᵗ F); let u ← ($ᵗ Fˣ); pure (repairEquiv (r, u))) =ᵈ
      ($ᵗ (Fˣ × F) : ProbComp (Fˣ × F)) :=
    SampleableType.evalDistEq_uniformSample_pair_of_bijective
      (f := fun r u => repairEquiv (r, u)) repairEquiv.bijective
  have hp : (fun p : Fˣ × F => (p.1 : F)) <$> ($ᵗ (Fˣ × F) : ProbComp (Fˣ × F)) =ᵈ
      ((fun u : Fˣ => (u : F)) <$> ($ᵗ Fˣ : ProbComp Fˣ)) := by
    rw [SampleableType.uniformSample_prod_eq_bind]
    conv_rhs => rw [← bind_pure_comp]
    simp only [map_bind, map_pure]
    exact EvalDistEq.bind_right _ fun u => EvalDistEq.bind_const _ _
  simpa only [map_bind, map_pure, repairEquiv_value] using
    (he.map (fun p : Fˣ × F => (p.1 : F))).trans hp

/-- The repaired law remains equal under any probabilistic continuation. -/
theorem repair_uniform_bind {A : Type} (next : F → ProbComp A) :
    (do let r ← ($ᵗ F); let u ← ($ᵗ Fˣ); next (repair r u)) =ᵈ (do let u ← ($ᵗ Fˣ); next u) := by
  simpa only [bind_assoc, pure_bind, bind_map_left] using (repair_uniform (F := F)).bind_left next

end Schnorr.NonzeroNonce
