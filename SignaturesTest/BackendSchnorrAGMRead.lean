import Signatures.Runtime.BackendSchnorrAGMReadBudget
import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

open OracleComp OracleSpec PFunctor Schnorr.AGM
open Signatures.Runtime Signatures.Runtime.BackendProgram Signatures.Runtime.SchnorrAGM.Native

namespace SignaturesTest.BackendSchnorrAGMRead

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

-- A hit restores every metadata field, including a preexisting malformed flag.
-- The late explanation would be bad with challenge two; it must be ignored.
example : (Read.code rep data cost primitive sampler).denote
    ((7, 1), (0, 5), [((7, 1), (2, true, 1, 0)), ((7, 1), (3, true, 0, 5))],
      [(1, 0), (0, 1), (4, 6)], [8, 9], true, false) =
    pure (2, [((7, 1), (2, true, 1, 0)), ((7, 1), (3, true, 0, 5))],
      [(1, 0), (0, 1), (4, 6)], [8, 9], true, false) := by
  rw [Read.denote, cacheAccess_denote]
  rfl

-- The entire costed wrapper, including its local adapters, is independent of
-- the sampler on a hit, even for a signing-programmed entry with no explanation.
example (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat) :
    (Read.code rep data cost primitive sampler).run control queryCost
      ((7, 1), (0, 5), [((7, 1), (2, false, 0, 0))], [(1, 0), (0, 1)], [7], false, true) =
    (Read.code rep data cost primitive other).run control queryCost
      ((7, 1), (0, 5), [((7, 1), (2, false, 0, 0))], [(1, 0), (0, 1)], [7], false, true) := by
  apply Read.hit_run
  rfl

-- A new commitment samples even when the message is already present. The
-- sampled challenge makes the recorded denominator vanish; only the cache and
-- bad flag change. This exercises all outer tuple projections on the miss path.
example (hs : sampler.denote () = pure (2 : F)) :
    (Read.code rep data cost primitive sampler).denote
      ((7, 2), (0, 5), [((7, 1), (3, false, 0, 0))], [(1, 0), (0, 1)], [7], false, false) =
    pure (2, [((7, 2), (2, true, 0, 5)), ((7, 1), (3, false, 0, 0))],
      [(1, 0), (0, 1)], [7], false, true) := by
  rw [Read.denote, cacheAccess_denote]
  have h : ((7 : Nat), (1 : F)) ≠ (7, 2) := by decide
  simp only [Read.packValue, Read.setupValue, cacheMap, h, ite_false, hs, map_pure,
    freshValue, Read.returnValue]
  rfl

end Execution

open Lean Meta in
run_meta do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``Read.setupExpression_value, ``Read.returnExpression_value,
      ``Read.denote, ``Read.source, ``Read.hit_run, ``Read.description,
      ``Read.history_size, ``Read.pack_property, ``Read.return_property,
      ``Read.input_size, ``Read.coreInput_size, ``Read.coreOutput_size,
      ``Read.retainedInput_size, ``Read.retainedOutput_size, ``Read.output_size,
      ``Read.setup_cost, ``Read.finish_cost, ``Read.bound] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"
  for name in #[``Read.code, ``Read.source, ``Read.bound] do
    forallTelescope (← getConstInfo name).type fun params _ => do
      for param in params do
        let type ← inferType param
        if type.isAppOf ``Finite || type.isAppOf ``Fintype then
          throwError "{name}: unexpected finite-domain premise"
        for forbidden in #[``Read.code, ``Read.readTime, ``Read.setup, ``Read.finish,
            ``cacheAccess, ``cacheTime, ``freshSample, ``comparison] do
          if (type.find? (fun e => e.isConstOf forbidden)).isSome then
            throwError "{name}: assumes a completed component's efficiency"

end SignaturesTest.BackendSchnorrAGMRead
