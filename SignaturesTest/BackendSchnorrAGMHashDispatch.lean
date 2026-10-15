import Signatures.Runtime.BackendSchnorrAGMHashDispatchBudget
import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

open OracleComp OracleSpec PFunctor
open Signatures.Runtime Signatures.Runtime.BackendProgram Signatures.Runtime.SchnorrAGM.Native

namespace SignaturesTest.BackendSchnorrAGMHashDispatch

private instance : Fact (Nat.Prime 7) := ⟨by decide⟩
private abbrev F := ZMod 7

section Execution

variable {C : StepClass} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass C} [Q.HasCategory] [Q.HasProd] [Q.HasSum]
  {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F F F Nat Nat))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F F F Nat Nat cost).execute instr))
  (sampler other : Code Q unifSpec iface rep.data.unit (rep.ty scalar))

-- Duplicate points still form an invalid request. Rejection changes only the
-- malformed flag; the cached explanation, basis, signed history and bad remain.
example : (HashDispatch.code rep data cost primitive sampler).denote
    (7, [1, 1], [[3, 5]], [((7, 1), (2, true, 1, 0))], [(1, 0), (0, 1)], [8], false, true) =
    pure (0, [((7, 1), (2, true, 1, 0))], [(1, 0), (0, 1)], [8], true, true) := by
  rw [HashDispatch.denote]

-- A missing coefficient row rejects, even when the group list is a singleton.
example : (HashDispatch.code rep data cost primitive sampler).denote
    (7, [1], [], [], [(1, 0), (0, 1)], [], false, false) =
    pure (0, [], [(1, 0), (0, 1)], [], true, false) := by
  rw [HashDispatch.denote]

-- Multiple empty rows are invalid. This checks the actual costed run rather
-- than only erasing sampling effects from its value distribution.
example (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat) :
    (HashDispatch.code rep data cost primitive sampler).run control queryCost
      (7, [1], [[], []], [], [(1, 0), (0, 1)], [], false, false) =
    (HashDispatch.code rep data cost primitive other).run control queryCost
      (7, [1], [[], []], [], [(1, 0), (0, 1)], [], false, false) := by
  apply HashDispatch.malformed_run
  rfl

-- Exactly one empty row is accepted and zero-padded by the source convention.
example (hs : sampler.denote () = pure (2 : F)) :
    (HashDispatch.code rep data cost primitive sampler).denote
      (7, [2], [[]], [], [(1, 0), (0, 1)], [], false, false) =
    pure (2, [((7, 2), (2, true, 0, 0))], [(1, 0), (0, 1)], [], false, false) := by
  rw [HashDispatch.denote]
  dsimp only
  rw [Hash.denote, Read.denote, cacheAccess_denote]
  simp only [Hash.prepareValue, Read.packValue, Read.setupValue, cacheMap, hs, map_pure,
    freshValue, Read.returnValue]
  rfl

-- A valid hash keeps the first explanation on an existing entry, even when
-- the later vector would have made the exceptional-challenge condition true.
example : (HashDispatch.code rep data cost primitive sampler).denote
    (7, [1], [[0, 5]], [((7, 1), (2, true, 1, 0))], [(1, 0), (0, 1)], [8], true, false) =
    pure (2, [((7, 1), (2, true, 1, 0))], [(1, 0), (0, 1)], [8], true, false) := by
  rw [HashDispatch.denote]
  dsimp only
  rw [Hash.denote, Read.denote, cacheAccess_denote]
  rfl

end Execution

open Lean Meta in
run_meta do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``HashDispatch.prepareExpression_value, ``HashDispatch.rejectExpression_value,
      ``HashDispatch.denote, ``HashDispatch.malformed_run, ``HashDispatch.source,
      ``HashDispatch.description, ``HashDispatch.decoded_property, ``HashDispatch.coefficient_size,
      ``HashDispatch.input_size, ``HashDispatch.prepare_size, ``HashDispatch.reject_property,
      ``HashDispatch.prepare_cost, ``HashDispatch.route_property, ``HashDispatch.route_size,
      ``HashDispatch.route_cost, ``HashDispatch.reject_cost, ``HashDispatch.bound] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"
  for name in #[``HashDispatch.code, ``HashDispatch.source, ``HashDispatch.bound] do
    forallTelescope (← getConstInfo name).type fun params _ => do
      for param in params do
        let type ← inferType param
        if type.isAppOf ``Finite || type.isAppOf ``Fintype then
          throwError "{name}: unexpected finite-domain premise"
        for forbidden in #[``HashDispatch.code, ``HashDispatch.prepare, ``HashDispatch.route,
            ``HashDispatch.reject, ``HashDispatch.dispatchTime, ``HashDispatch.prepareTime,
            ``Hash.code, ``Hash.hashTime, ``ListSingleton.scan, ``ListSingleton.scanTime] do
          if (type.find? (fun e => e.isConstOf forbidden)).isSome then
            throwError "{name}: assumes a completed component's efficiency"

end SignaturesTest.BackendSchnorrAGMHashDispatch
