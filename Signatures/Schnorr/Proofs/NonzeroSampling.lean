import Signatures.Schnorr.Spec.NonzeroNonce
import Mathlib.FieldTheory.Finite.Basic
import VCVio.OracleComp.QueryTracking.RandomOracle.DeferredSampling

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
    𝒮[do let r ← ($ᵗ F); let u ← ($ᵗ Fˣ); pure (repair r u)] =
      𝒮[(fun u : Fˣ => (u : F)) <$> ($ᵗ Fˣ)] := by
  have he := evalSPMF_map_bijective_uniform_cross (F × Fˣ) repairEquiv repairEquiv.bijective
  have hf := congrArg (Functor.map (fun p : Fˣ × F => (p.1 : F))) he
  have hp := congrArg (Functor.map (fun u : Fˣ => (u : F)))
    (evalSPMF_map_fst_uniformSample_prod (α := Fˣ) (β := F))
  simp only [← evalSPMF_map, Functor.map_map] at hf hp
  rw [hf.symm] at hp
  have hpair : ($ᵗ (F × Fˣ)) = (do let r ← ($ᵗ F); let u ← ($ᵗ Fˣ); pure (r, u)) := by
    change (Prod.mk <$> ($ᵗ F) <*> ($ᵗ Fˣ)) = _
    simp only [seq_eq_bind_map, bind_map_left, bind_pure_comp]
  rw [hpair] at hp
  simpa only [map_bind, map_pure, repairEquiv_value] using hp

/-- The repaired law remains equal under any probabilistic continuation. -/
theorem repair_uniform_bind {A : Type} (next : F → ProbComp A) :
    𝒮[do let r ← ($ᵗ F); let u ← ($ᵗ Fˣ); next (repair r u)] =
      𝒮[do let u ← ($ᵗ Fˣ); next u] := by
  have h := congrArg (fun law => law >>= fun x => evalSPMF (next x)) (repair_uniform (F := F))
  simpa only [← evalSPMF_bind, bind_assoc, pure_bind, bind_map_left] using h

end Schnorr.NonzeroNonce
