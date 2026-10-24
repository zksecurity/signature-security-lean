import Proofs.Runtime.Caliper.InteractiveInvariantBounds

/-! Reachable-domain refinements admit mathematical views only when their
encodings are identical. The invariant follows the input view; code, time,
queries and stored bytes are unchanged. -/
namespace Signatures.Runtime.CaliperBackend.Interactive
open Caliper OracleComp OracleSpec
variable {w : Nat} {I A B D : Type} {spec : OracleSpec I} {port : Port w spec} {cost : WordIO.Costs}
    {predicate : A → Prop} {input : Representation w A} {output : Representation w B}
    {source : A → OracleComp spec B} {target : Code w}

/-- A source invariant may justify a new output view on every reachable answer.
The fallback of a total mathematical view is irrelevant only after that support
condition is proved. The code still produces exactly the same encoded bytes. -/
theorem Refines.viewOutputOnSupport (refined : Refines port cost input output source target)
    (newOutput : Representation w D) (view : B → D)
    (sameBytes : ∀ value, ∀ answer ∈ support (source value),
      newOutput.encoding.encode (view answer) = output.encoding.encode answer) :
    Refines port cost input newOutput (fun value => view <$> source value) target := by
  intro tape value before represented
  simpa only [id_map] using (refined tape value before represented).with_support.map view id (by
    intro answer result related
    obtain ⟨finished, rfl, holds, remaining, execution⟩ := related.1
    exact ⟨finished, rfl,
      ⟨holds.1, holds.2.1.trans (sameBytes value answer related.2.1).symm, holds.2.2⟩,
      remaining, execution⟩)

theorem RefinesOn.viewOutput (refined : RefinesOn predicate port cost input output source target)
    (newOutput : Representation w D) (view : B → D)
    (sameBytes : ∀ value, newOutput.encoding.encode (view value) = output.encoding.encode value) :
    RefinesOn predicate port cost input newOutput (fun value => view <$> source value) target := by
  intro tape value valid before represented
  simpa only [id_map] using (refined tape value valid before represented).map view id (by
    intro answer result realization
    obtain ⟨finished, rfl, holds, remaining, execution⟩ := realization
    exact ⟨finished, rfl, ⟨holds.1, holds.2.1.trans (sameBytes answer).symm, holds.2.2⟩, remaining, execution⟩)

theorem RefinesOn.viewInput (refined : RefinesOn predicate port cost input output source target)
    (newInput : Representation w D) (view : D → A)
    (sameBytes : ∀ value, input.encoding.encode (view value) = newInput.encoding.encode value) :
    RefinesOn (fun value => predicate (view value)) port cost newInput output (fun value => source (view value)) target := by
  intro tape value valid before represented
  exact refined tape (view value) valid before
    ⟨represented.1, represented.2.1.trans (sameBytes value).symm, represented.2.2⟩

theorem TimeBoundOn.viewInput {budget : Nat} (bounded : TimeBoundOn predicate port cost input target budget)
    (newInput : Representation w D) (view : D → A)
    (sameBytes : ∀ value, input.encoding.encode (view value) = newInput.encoding.encode value) :
    TimeBoundOn (fun value => predicate (view value)) port cost newInput target budget := by
  intro tape value valid before represented finished reached
  exact bounded tape (view value) valid before
    ⟨represented.1, represented.2.1.trans (sameBytes value).symm, represented.2.2⟩ finished reached
end Signatures.Runtime.CaliperBackend.Interactive
