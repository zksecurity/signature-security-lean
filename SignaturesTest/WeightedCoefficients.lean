import Proofs.Runtime.BackendWeightedCoefficients
import Proofs.Runtime.BackendWeightedEvaluateEncoding
import Proofs.Runtime.BackendWeightedCoefficientBudget
import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

open OracleComp OracleSpec PFunctor
open Signatures.Runtime Signatures.Runtime.BackendProgram Signatures.Runtime.WeightedAGM

namespace SignaturesTest.WeightedCoefficients

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private abbrev field := ZMod 5
private abbrev model := arithmetic field field field Nat Bool PrimitiveCosts.unit

-- The log is backwards. Equal messages in separate reply occurrences keep
-- separate coefficients. Zero and missing coefficients retain all their terms.
example : ((Coefficients.signedTerms (Terms.oops 2)).run model
    ([((3, 38), 0), ((2, 37), 4), ((2, 37), 2)], [2, 0], ())).value =
      [((37, 0), 2), ((37, 1), 4), ((37, 2), 3),
       ((37, 0), 0), ((37, 1), 0), ((37, 2), 0),
       ((38, 0), 0), ((38, 1), 0), ((38, 2), 0)] := by decide

-- A surplus coefficient creates no extra signing reply or weighted base.
example : ((Coefficients.signedTerms (Terms.oops 1)).run model
    ([((2, 37), 4)], [3, 4, 2], ())).value = [((37, 0), 3), ((37, 1), 1)] := by decide

example : ((Coefficients.signedTerms (Terms.oops 0)).run model
    ([], [3, 4, 2], ())).value = [] := by decide

-- Proximity includes the constant coordinate and keeps a zero vector entry.
example : ((Coefficients.signedTerms (Terms.proximity 2)).run model
    ([(((2, (0, ())), 37), 4)], [3], ())).value =
      [((0, 37), 3), ((1, 37), 1), ((2, 37), 0)] := by decide

example : ((Coefficients.signedTerms (Terms.proximity 0)).run model
    ([(((), 37), 4)], [3, 2], ())).value = [((0, 37), 3)] := by decide

-- A zero coefficient retains every generated term and the earlier accumulator.
-- The unrelated context contains a different key and scalar list.
example : ((Coefficients.expandStep (Terms.oops 1) (Γ := [key, .list scalar])).run model
    ((((2, 37), 4), 0), [((99, 1), 3)], 101, [4, 2], ())).value =
      [((37, 1), 0), ((37, 0), 0), ((99, 1), 3)] := by decide

-- With no signing replies the generated-term loop is never entered, including
-- at nonzero degree. The concrete bound charges preparation and routing only.
example (overhead : Nat → Nat) (w c d i m o e s a z : Nat) :
    Coefficients.oopsCoefficientTime overhead w 0 c d i m o e s a z =
      Coefficients.oopsCoefficientTime overhead w 0 c 0 i m o e s a z := by
  simp [Coefficients.oopsCoefficientTime, Coefficients.coefficientTime,
    Coefficients.coefficientWidth, Coefficients.expandRowsTime, Coefficients.expandRowsWidth]

section Compiled

variable {C : StepClass} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass C} [Q.HasCategory] [Q.HasProd] [Q.HasSum]
  {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase field field field Nat Bool))
  (data : DataCode Q rep.data) (sampling : MachineCompiler.SamplingImplementation Q iface rep)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) (model.execute instr))

-- The original Option coordinate encoding reaches both native mask components.
-- The first term has zero weight; a repeated coordinate uses the first binding,
-- and the entire shadowed cache survives unchanged.
example : (Evaluate.backendBad rep data PrimitiveCosts.unit primitive sampling (.proximity 1)).denote
    (([(((none, 37) : Option (Fin 1) × Nat), (0 : field)), ((some 0, 37), 2), ((some 0, 37), 4)].map
       (Prod.map Weights.encodeProximityKey id),
      Prod.map Weights.encodeProximityKey id (((none, 9999) : Option (Fin 1) × Nat), (0 : field)), ()),
      [(((none, 37) : Option (Fin 1) × Nat), ((2, 1) : field × field)),
       ((some 0, 37), (3, 4)), ((some 0, 37), (1, 2))].map (Prod.map Weights.encodeProximityKey id)) =
    pure (((3, 4) : field × field),
      [(((none, 37) : Option (Fin 1) × Nat), ((2, 1) : field × field)),
       ((some 0, 37), (3, 4)), ((some 0, 37), (1, 2))].map (Prod.map Weights.encodeProximityKey id)) := by
  rw [Evaluate.proximity_backendBad_source]
  rw [Model.LazyAGM.WeightedReduction.evalTerms_cached_eq _ _ (by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    all_goals exact ⟨_, rfl⟩)]
  rfl

end Compiled

open Lean Meta

run_meta do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``privateRead_encoded, ``evalTerms_encoded,
      ``Evaluate.backendGood_source_encoded, ``Evaluate.backendBad_source_encoded,
      ``Evaluate.proximity_backendGood_source, ``Evaluate.proximity_backendBad_source,
      ``Evaluate.backendGood_cached, ``Evaluate.backendBad_cached,
      ``Coefficients.source_signedTerms_map, ``Coefficients.scalePrepend_denote,
      ``Coefficients.expandStep_denote, ``Coefficients.expandRows_denote, ``Coefficients.signedTerms_denote,
      ``Coefficients.oops_signedTerms_denote, ``Coefficients.proximity_signedTerms_denote,
      ``Coefficients.signedTerms_description, ``Coefficients.oopsCode_description,
      ``Coefficients.proximityCode_description, ``Coefficients.source_signedTerms_length,
      ``Coefficients.signedTerms_output_size, ``Coefficients.oops_signedTerms_output_size,
      ``Coefficients.proximity_signedTerms_output_size,
      ``Coefficients.scalePrepend_time, ``Coefficients.scalePrepend_cost,
      ``Coefficients.expandStep_time, ``Coefficients.expandRows_time, ``Coefficients.signedTerms_time,
      ``Coefficients.oopsCode_cost, ``Coefficients.proximityCode_cost] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"
  for name in #[``evalTerms_encoded, ``Evaluate.proximity_backendGood_source,
      ``Evaluate.proximity_backendBad_source, ``Coefficients.signedTerms_denote,
      ``Coefficients.oopsCode, ``Coefficients.proximityCode,
      ``Coefficients.oopsCode_description, ``Coefficients.proximityCode_description,
      ``Coefficients.signedTerms_output_size, ``Coefficients.oops_signedTerms_output_size,
      ``Coefficients.proximity_signedTerms_output_size,
      ``Coefficients.scalePrepend_time, ``Coefficients.scalePrepend_cost,
      ``Coefficients.oopsCode_cost, ``Coefficients.proximityCode_cost] do
    forallTelescope (← getConstInfo name).type fun params _ => do
      for param in params do
        let type ← inferType param
        if type.isAppOf ``Finite || type.isAppOf ``Fintype then
          throwError "{name}: finite topic/slot/message domain required"
        for forbidden in #[``Bounds, `Signatures.Runtime.GeneralCaller.Budget] do
          if type.find? (fun e => e.isConstOf forbidden) |>.isSome then
            throwError "{name}: supplied completed-program budget"

-- The final scheme costs must derive generator/fold budgets, even though the
-- shared composition helpers accept local component bounds.
run_meta do
  for name in #[``Coefficients.oopsCode_cost, ``Coefficients.proximityCode_cost] do
    forallTelescope (← getConstInfo name).type fun params _ => do
      for param in params do
        let type ← inferType param
        for forbidden in #[``Expression.compileBound, ``Terms.oopsCode, ``Terms.proximityCode,
            ``Coefficients.scalePrepend, ``Coefficients.expandRows, ``Coefficients.signedTerms] do
          if (type.find? (fun e => e.isConstOf forbidden)).isSome then
            throwError "{name}: supplied generator or expansion cost premise: {forbidden}"

end SignaturesTest.WeightedCoefficients
