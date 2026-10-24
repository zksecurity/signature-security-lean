import Proofs.Runtime.BackendSchnorrAGMCacheBudget
import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

open OracleComp OracleSpec PFunctor Schnorr.AGM
open Signatures.Runtime Signatures.Runtime.BackendProgram Signatures.Runtime.SchnorrAGM.Native

namespace SignaturesTest.BackendSchnorrAGMCache

private instance : Fact (Nat.Prime 7) := ⟨by decide⟩
private abbrev F := ZMod 7

-- The explanation is fixed before sampling. Challenge two is bad for secret
-- coefficient five, but not for zero. An already-set flag remains set.
example : freshValue ((2 : F), (0, 5), false) = ((2, true, 0, 5), (0, 5), true) := by decide
example : freshValue ((2 : F), (1, 0), false) = ((2, true, 1, 0), (1, 0), false) := by decide
example : freshValue ((2 : F), (1, 0), true) = ((2, true, 1, 0), (1, 0), true) := by decide

example : decodeEntry (encodeEntry (⟨2, none⟩ : Reduction.Entry F)) = ⟨2, none⟩ :=
  decode_encodeEntry _

-- Ignored scalar slots of a programmed entry do not become an explanation.
example : (decodeEntry ((2 : F), false, 3, 4)).representation = none := rfl

section Execution

variable {C : StepClass} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass C} [Q.HasCategory] [Q.HasProd] [Q.HasSum]
  {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F F F Nat Nat))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F F F Nat Nat cost).execute instr))
  (sampler other : Code Q unifSpec iface rep.data.unit (rep.ty scalar))

-- Same message and commitment; the earlier explanation wins. The late
-- explanation has a vanishing denominator, but a cache hit must not set bad.
example : (cacheAccess rep data cost primitive sampler).denote
    (((7, 1), (0, false, 0, 0), [((7, 1), (2, true, 1, 0)), ((7, 1), (3, true, 0, 5))], ()),
      ((0, 5), false)) =
    pure (((2, true, 1, 0), [((7, 1), (2, true, 1, 0)), ((7, 1), (3, true, 0, 5))]), ((0, 5), false)) := by
  rw [cacheAccess_denote]
  rfl

-- No sampler call even in the costed run. A different implementation of all
-- randomness has no effect on either result or time for the cached point.
example (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat) :
    (cacheAccess rep data cost primitive sampler).run control queryCost
      (((7, 1), (0, false, 0, 0), [((7, 1), (2, true, 1, 0))], ()), ((0, 5), false)) =
    (cacheAccess rep data cost primitive other).run control queryCost
      (((7, 1), (0, false, 0, 0), [((7, 1), (2, true, 1, 0))], ()), ((0, 5), false)) := by
  apply cacheAccess_hit_run
  rfl

-- A signing-programmed entry retains its tag and cached challenge.
example : (cacheAccess rep data cost primitive sampler).denote
    (((7, 1), (0, true, 4, 4), [((7, 1), (2, false, 0, 0))], ()), ((0, 5), false)) =
    pure (((2, false, 0, 0), [((7, 1), (2, false, 0, 0))]), ((0, 5), false)) := by
  rw [cacheAccess_denote]
  rfl

-- A changed commitment is a new key even for the same message. The dummy
-- default entry never leaks into the new entry; the supplied affine pair does.
example : (cacheAccess rep data cost primitive sampler).denote
    (((7, 2), (6, false, 4, 4), [((7, 1), (2, true, 1, 0))], ()), ((0, 5), false)) =
    (fun c : F => (((c, true, 0, 5), [((7, 2), (c, true, 0, 5)), ((7, 1), (2, true, 1, 0))]),
      ((0, 5), decide (5 + c = 0)))) <$> sampler.denote () := by
  rw [cacheAccess_denote]
  have h : ((7 : Nat), (1 : F)) ≠ (7, 2) := by decide
  simp only [cacheMap, h, ite_false, freshValue, Bool.false_or]

end Execution

open Lean Meta in
run_meta do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``decode_encodeState, ``encodeState_injective, ``cacheMap_encode,
      ``keyEquality_value, ``comparison_cost, ``comparison_description,
      ``freshExpression_value, ``freshCode_cost, ``freshSample_denote,
      ``freshSample_bound, ``freshSample_description, ``cacheAccess_denote,
      ``cacheAccess_read, ``cacheAccess_hit_run, ``cacheAccess_bound, ``cacheAccess_description] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"
  for name in #[``cacheAccess, ``cacheAccess_read, ``cacheAccess_bound] do
    forallTelescope (← getConstInfo name).type fun params _ => do
      for param in params do
        let type ← inferType param
        if type.isAppOf ``Finite || type.isAppOf ``Fintype then
          throwError "{name}: unexpected finite-domain premise"
        for forbidden in #[``cacheAccess, ``cacheTime] do
          if (type.find? (fun e => e.isConstOf forbidden)).isSome then
            throwError "{name}: assumes its own completed-cache certificate"

end SignaturesTest.BackendSchnorrAGMCache
