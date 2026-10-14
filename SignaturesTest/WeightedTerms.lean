import Signatures.Runtime.BackendWeightedTerms
import Signatures.Runtime.BackendWeightedTermsContext
import Signatures.Runtime.BackendWeightedKeyEquality
import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

open OracleComp OracleSpec PFunctor Signatures.Runtime Signatures.Runtime.BackendProgram
open Signatures.Runtime.WeightedAGM.Terms

namespace SignaturesTest.WeightedTerms

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private abbrev field := ZMod 5
private def arithmeticModel := arithmetic field field field Nat Bool PrimitiveCosts.unit

-- A zero scalar still emits every degree, including the constant term. Dropping
-- zero-weight entries would change which private bases are sampled.
example : ((oops 3).run arithmeticModel ((0, 1000000), ())).value =
    [((1000000, 0), 1), ((1000000, 1), 0), ((1000000, 2), 0), ((1000000, 3), 0)] := by
  decide

-- No multiplication wraparound may change the degree tags or term order.
example : ((oops 3).run arithmeticModel ((2, 37), ())).value =
    [((37, 0), 1), ((37, 1), 2), ((37, 2), 4), ((37, 3), 3)] := by decide

example : ((oops 0).run arithmeticModel ((4, 37), ())).value = [((37, 0), 1)] := by decide

-- A nonempty retained context contains different scalars and a different topic;
-- the helper must continue using its current message and running power.
example : ((oopsFrom 3 3 1 (Γ := [scalar, key, .list scalar])).run arithmeticModel
    (4, (2, 37), 3, 88, [2], ())).value =
      [((37, 1), 4), ((37, 2), 3), ((37, 3), 1)] := by decide

example : ((proximity 3).run arithmeticModel (((4, 0, 2, ()), 37), ())).value =
    [((0, 37), 1), ((1, 37), 4), ((2, 37), 0), ((3, 37), 2)] := by decide

example : ((proximity 0).run arithmeticModel (((), 37), ())).value = [((0, 37), 1)] := by decide

example : ((proximityFrom 3 2 2 (Γ := [scalar, key, .list scalar])).run arithmeticModel
    (((4, 2, ()), 37), 3, 88, [2], ())).value = [((2, 37), 4), ((3, 37), 2)] := by decide

-- Dimension zero has a constant term; an empty term list is not a valid replacement.
example : ((proximity 0).run arithmeticModel (((), 37), ())).value ≠ [] := by decide

-- The complete generators also work inside retained lists and an unrelated key.
example : (((oops 2).weakenTail [.list scalar, key]).run arithmeticModel
    ((2, 37), [4, 4], 99, ())).value = [((37, 0), 1), ((37, 1), 2), ((37, 2), 4)] := by decide

example : (((proximity 0).weakenTail [.list scalar, key]).run arithmeticModel
    (((), 37), [2, 3], 99, ())).value = [((0, 37), 1)] := by decide

section Compiled

variable {C : StepClass} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass C} [Q.HasCategory] [Q.HasProd] [Q.HasSum]
  {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase field field field Nat Bool))
  (data : DataCode Q rep.data)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) (arithmeticModel.execute instr))

-- Exercise the complete compiled entry programs with the real scheme terms as
-- their semantic indices, in a backend whose implementations are supplied individually.
example : (Code.atomic (iface := iface) (oopsCode rep data PrimitiveCosts.unit primitive 3)).denote
    ((2, 37), ()) = pure [((37, 0), 1), ((37, 1), 2), ((37, 2), 4), ((37, 3), 3)] := by
  change pure (OOPS.LazyAGM.terms 3 ((2 : field), (37 : Nat))) = _
  congr 1

example : (Code.atomic (iface := iface) (proximityCode rep data PrimitiveCosts.unit primitive 3)).denote
    (((4, 0, 2, ()), 37), ()) = pure [((0, 37), 1), ((1, 37), 4), ((2, 37), 0), ((3, 37), 2)] := by
  change pure ((Proximity.LazyAGM.terms
    (Weights.proximityMessageEquiv (F := field) (G₁ := field) (G₂ := field) (M := Bool)
      3 (((4, 0, 2, ()), (37 : Nat))))).map (Prod.map Weights.encodeProximityKey id)) = _
  congr 1

-- Cache key equality must distinguish both components, including Proximity's
-- constant coordinate. These tests execute the compiled comparison syntax.
example : (Code.atomic (iface := iface)
    (Expression.compile rep data arithmeticModel primitive (AGM.KeyEquality.oops 3))).denote
      ((37, 0), (37, 1), ()) = pure false := rfl

example : (Code.atomic (iface := iface)
    (Expression.compile rep data arithmeticModel primitive (AGM.KeyEquality.oops 3))).denote
      ((37, 1), (38, 1), ()) = pure false := rfl

example : (Code.atomic (iface := iface)
    (Expression.compile rep data arithmeticModel primitive (AGM.KeyEquality.oops 3))).denote
      ((37, 1), (37, 1), ()) = pure true := rfl

example : (Code.atomic (iface := iface)
    (Expression.compile rep data arithmeticModel primitive (AGM.KeyEquality.proximity 3))).denote
      ((0, 37), (1, 37), ()) = pure false := rfl

example : (Code.atomic (iface := iface)
    (Expression.compile rep data arithmeticModel primitive (AGM.KeyEquality.proximity 3))).denote
      ((1, 37), (1, 38), ()) = pure false := rfl

end Compiled

open Lean Meta

run_meta do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``oopsFrom_value, ``oops_value, ``proximityFrom_value, ``proximity_value,
      ``oops_steps_le, ``proximity_steps_le, ``oops_description, ``proximity_description,
      ``oopsFrom_output_size, ``proximityFrom_output_size, ``oops_output_size, ``proximity_output_size,
      ``oopsFrom_native_time, ``proximityFrom_native_time,
      ``oopsFrom_weakenTail, ``proximityFrom_weakenTail, ``oops_weakenTail, ``proximity_weakenTail,
      ``oops_weakenTail_time, ``proximity_weakenTail_time,
      ``oopsCode_size, ``proximityCode_size, ``oopsCode_cost, ``proximityCode_cost,
      ``tuple_size, ``proximityCode_cost_of_atoms,
      ``AGM.KeyEquality.oops_cost, ``AGM.KeyEquality.proximity_cost,
      ``AGM.KeyEquality.oops_description, ``AGM.KeyEquality.proximity_description,
      ``AGM.KeyEquality.oops_code_size, ``AGM.KeyEquality.proximity_code_size] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"
  for name in #[``oopsCode, ``proximityCode, ``oopsCode_size, ``proximityCode_size,
      ``oopsCode_cost, ``proximityCode_cost, ``proximityCode_cost_of_atoms,
      ``oops_weakenTail_time, ``proximity_weakenTail_time,
      ``AGM.KeyEquality.oops_cost, ``AGM.KeyEquality.proximity_cost] do
    forallTelescope (← getConstInfo name).type fun params _ => do
      for param in params do
        let type ← inferType param
        if type.isAppOf ``Finite || type.isAppOf ``Fintype then
          throwError "{name}: term generation must not require a finite domain"
        for forbidden in #[`Signatures.Runtime.BackendProgram.Bounds,
            `Signatures.Runtime.GeneralCaller.Budget] do
          if type.find? (fun e => e.isConstOf forbidden) |>.isSome then
            throwError "{name}: cannot assume the finished generator's budget"

end SignaturesTest.WeightedTerms
