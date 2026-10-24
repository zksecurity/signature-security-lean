import Proofs.Runtime.Caliper.SchnorrROMNonzeroSigningSamplerBounds

/-! The lawful canonical sampler of `Fˣ` associated with the enumerated index:
the uniform index below `bound` is transported along
`Fin bound ≃ {j // j ≠ index 0} ≃ {x : F // x ≠ 0} ≃ Fˣ`, where the first map is
`Fin.succAbove (index 0)`. Both executed nonzero draws are exactly this query
program after coercion to `F`. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROMTape.PrivateSampler.Enumerated.Nonzero
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat} {F : Type} [GroupWithZero F] (params : Parameters w F)

/-- A nontrivial scalar domain has a nonzero element, so `bound ≥ 1`. -/
theorem bound_pos : 0 < params.bound := by
  by_contra small
  have zeroLt := (params.index 0).isLt
  have oneLt := (params.index 1).isLt
  have same : params.index 0 = params.index 1 := Fin.ext (by omega)
  exact zero_ne_one (params.index.injective same)

/-- The finite index of the nonzero scalars, through the zero-skipping map. -/
def unitsEquiv : Fin (params.bound - 1 + 1) ≃ Fˣ :=
  (finCongr (Nat.sub_add_cancel (bound_pos params))).trans
    ((finSuccAboveEquiv (zeroIndex params)).trans
      ((params.index.symm.subtypeEquiv (fun j => by
        constructor
        · intro different same
          exact different (by unfold zeroIndex; rw [← same, Equiv.apply_symm_apply])
        · intro different same
          exact different (by rw [same]; exact params.index.symm_apply_apply 0))).trans
        unitsEquivNeZero.symm))

theorem unitsEquiv_val (answer : Fin (params.bound - 1 + 1)) :
    ((unitsEquiv params answer : Fˣ) : F) = (scalarOf params (bound_pos params) answer.val).val := by
  have small : answer.val < params.bound := by
    have := answer.isLt; have := bound_pos params; omega
  change params.index.symm ((zeroIndex params).succAbove ⟨answer.val, _⟩) =
    params.index.symm ((zeroIndex params).succAbove ⟨answer.val % params.bound, _⟩)
  exact congrArg (fun k => params.index.symm ((zeroIndex params).succAbove k)) (Fin.ext (Nat.mod_eq_of_lt small).symm)

/-- The canonical uniform sampler of `Fˣ` for the enumerated index. -/
@[reducible] def unitsSampleable : SampleableType Fˣ :=
  letI : SampleableType (Fin (params.bound - 1 + 1)) := SampleableType.Fin (params.bound - 1)
  SampleableType.ofEquiv (unitsEquiv params)

theorem units_query :
    letI := unitsSampleable params
    (fun a : Fˣ => (a : F)) <$> ($ᵗ Fˣ : ProbComp Fˣ) =
      (fun answer : Fin (params.bound - 1 + 1) => (scalarOf params (bound_pos params) answer.val).val) <$>
        (unifSpec.query (params.bound - 1) : ProbComp (Fin (params.bound - 1 + 1))) := by
  change (fun a : Fˣ => (a : F)) <$> (unitsEquiv params <$>
    (unifSpec.query (params.bound - 1) : ProbComp (Fin (params.bound - 1 + 1)))) = _
  rw [Functor.map_map]
  exact congrArg (· <$> _) (funext fun answer => unitsEquiv_val params answer)

/-- The direct nonzero draw is the canonical uniform draw of `Fˣ`. -/
theorem Direct.uniform :
    letI := unitsSampleable params
    Subtype.val <$> Direct.nonzeroSource params (bound_pos params) = (fun a : Fˣ => (a : F)) <$> ($ᵗ Fˣ : ProbComp Fˣ) := by
  rw [units_query, Direct.nonzeroSource, Functor.map_map]

/-- The replayed caller's query program is the canonical uniform draw of `Fˣ`. -/
theorem samples (input : (tape params).unit.Value) :
    letI := unitsSampleable params
    Subtype.val <$> original (layout params) (caller params (bound_pos params)) 1 (terminates params (bound_pos params)) input =
      (fun a : Fˣ => (a : F)) <$> ($ᵗ Fˣ : ProbComp Fˣ) := by
  rw [original_typed]
  exact Direct.uniform params

theorem Direct.nonzero (answer : (scalar params).Value)
    (reached : answer ∈ support (Direct.nonzeroSource params (bound_pos params))) : answer.val ≠ 0 := by
  simp only [Direct.nonzeroSource, support_map, Set.mem_image] at reached
  obtain ⟨_, _, rfl⟩ := reached
  exact scalarOf_ne params (bound_pos params) _

/-- The direct draw's complete local cost, including stored code and memory. -/
theorem Direct.within :
    letI := unitsSampleable params
    Interactive.Within (Fresh.port (tape params)) (tape params).unit (scalar params)
      807 4230 180 (fun _ => (fun a : Fˣ => (a : F)) <$> ($ᵗ Fˣ : ProbComp Fˣ)) := by
  have bounded := Interactive.within_of_refines_accounted (Direct.refines params (bound_pos params))
    (Direct.time_bound params (bound_pos params)) (Direct.code_words params (bound_pos params))
    (Direct.names params (bound_pos params)) (Direct.descriptionFits params (bound_pos params))
  exact bounded.congr (fun _ => Direct.uniform params)

end Signatures.Runtime.CaliperBackend.SchnorrROMTape.PrivateSampler.Enumerated.Nonzero
