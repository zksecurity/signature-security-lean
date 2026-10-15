import Signatures.Runtime.BackendSchnorrAGMSigningDispatchBudget
import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

open OracleComp OracleSpec PFunctor
open Signatures.Runtime Signatures.Runtime.BackendProgram Signatures.Runtime.SchnorrAGM.Native

namespace SignaturesTest.BackendSchnorrAGMSigningDispatch

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

-- Every nonempty group list rejects. The reply has no group element, and only
-- the malformed flag changes, preserving the cache and both histories.
example : (SigningDispatch.code rep data cost primitive sampler).denote
    ([1], [[], [3, 5]], 1, 2, 7, [((7, 1), (0, true, 1, 0))], [(1, 0), (0, 1)], [8], false, true) =
    pure ((0, []), [((7, 1), (0, true, 1, 0))], [(1, 0), (0, 1)], [8], true, true) := by
  rw [SigningDispatch.denote]
  simp only [List.cons_ne_nil, ite_false]
  rfl

-- Rejection never calls the scalar sampler, even in the full costed run and
-- for arbitrary coefficient rows. Their representation still enters the bound.
example (rows : List (List F)) (control : ControlCosts)
    (queryCost : (i : Nat) → unifSpec.Range i → Nat) :
    (SigningDispatch.code rep data cost primitive sampler).run control queryCost
      ([1, 1], rows, 1, 2, 7, [], [], [], false, false) =
    (SigningDispatch.code rep data cost primitive other).run control queryCost
      ([1, 1], rows, 1, 2, 7, [], [], [], false, false) := by
  apply SigningDispatch.malformed_run
  simp

-- Signing accepts an empty group list regardless of coefficient-row shape;
-- the actual reply constructor puts the commitment in a singleton group list.
example (hs : sampler.denote () = pure (2 : F)) :
    (SigningDispatch.code rep data cost primitive sampler).denote
      ([], [[], [3, 5], [1]], 1, 2, 7, [], [], [], true, false) =
    pure ((2, [5]), [((7, 5), (2, false, 0, 0))], [(2, 5)], [7], true, false) := by
  rw [SigningDispatch.denote]
  simp only [ite_true]
  rw [Signing.denote, hs]
  simp only [pure_bind, map_pure]
  rfl

-- A collision keeps the cached zero and the first explanation. The signing
-- response and chronological history still use the fresh draws.
example (hs : sampler.denote () = pure (2 : F)) :
    (SigningDispatch.code rep data cost primitive sampler).denote
      ([], [], 1, 2, 7, [((7, 5), (0, true, 1, 0)), ((7, 5), (4, false, 6, 5))],
        [(1, 0)], [7], false, true) =
    pure ((2, [5]), [((7, 5), (0, true, 1, 0)), ((7, 5), (4, false, 6, 5))],
      [(1, 0), (2, 5)], [7, 7], false, true) := by
  rw [SigningDispatch.denote]
  simp only [ite_true]
  rw [Signing.denote, hs]
  simp only [pure_bind, map_pure]
  rfl

end Execution

open Lean Meta in
run_meta do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``encode_decodeGroupReply, ``decode_encodeGroupReply,
      ``ListEmpty.denote, ``ListEmpty.scan_time, ``ListEmpty.cost, ``ListEmpty.description,
      ``SigningDispatch.prepareExpression_value, ``SigningDispatch.wrapExpression_value,
      ``SigningDispatch.rejectExpression_value, ``SigningDispatch.denote,
      ``SigningDispatch.malformed_run, ``SigningDispatch.source, ``SigningDispatch.description,
      ``SigningDispatch.wrap_property, ``SigningDispatch.reject_property,
      ``SigningDispatch.input_size, ``SigningDispatch.prepare_size, ``SigningDispatch.route_size,
      ``SigningDispatch.output_size, ``SigningDispatch.prepare_cost, ``SigningDispatch.route_cost,
      ``SigningDispatch.wrap_cost, ``SigningDispatch.reject_cost, ``SigningDispatch.bound] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"
  for name in #[``SigningDispatch.code, ``SigningDispatch.source, ``SigningDispatch.bound] do
    forallTelescope (← getConstInfo name).type fun params _ => do
      for param in params do
        let type ← inferType param
        if type.isAppOf ``Finite || type.isAppOf ``Fintype then
          throwError "{name}: unexpected finite-domain premise"
        for forbidden in #[``SigningDispatch.code, ``SigningDispatch.prepare, ``SigningDispatch.route,
            ``SigningDispatch.wrap, ``SigningDispatch.reject, ``SigningDispatch.dispatchTime,
            ``SigningDispatch.prepareTime, ``Signing.code, ``Signing.signingTime,
            ``ListEmpty.scan, ``ListEmpty.scanTime] do
          if (type.find? (fun e => e.isConstOf forbidden)).isSome then
            throwError "{name}: assumes a completed component's efficiency"

end SignaturesTest.BackendSchnorrAGMSigningDispatch
