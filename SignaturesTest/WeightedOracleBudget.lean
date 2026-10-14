import Signatures.Runtime.BackendWeightedOracleCallerBudget
import Signatures.Runtime.BackendWeightedOracleDescription
import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

open OracleComp OracleSpec PFunctor
open Signatures.Runtime Signatures.Runtime.BackendProgram Signatures.Runtime.WeightedAGM

namespace SignaturesTest.WeightedOracleBudget

set_option backward.isDefEq.respectTransparency false

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private abbrev field := ZMod 5
private abbrev model := arithmetic field field field Nat Bool PrimitiveCosts.unit
private abbrev spec := generalSpec (Nat × Fin 2) (field × Nat) field 3

-- The signing message depends on the first hash, and the last hash index depends
-- on the signature. Both domains contain arbitrary natural topics.
private def adaptive : OracleComp spec field := do
  let h : field ← spec.query (.inl (.inr (37, 0)))
  let s : field ← spec.query (.inr (h, 37))
  spec.query (.inl (.inr (37, if s = 0 then 1 else 0)))

section Native

variable {C : StepClass} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass C} [Q.HasCategory] [Q.HasProd] [Q.HasSum]
  {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase field field field Nat Bool))
  (data : DataCode Q rep.data) (sampling : MachineCompiler.SamplingImplementation Q iface rep)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) (model.execute instr))

-- Check all adaptive replies and the complete cache/log state. The shadowed
-- cache binding survives, and signing does not manufacture an explicit hash.
example : (simulateQ (NativeHandler.goodSource rep (.oops 1) data PrimitiveCosts.unit
    primitive sampling (randomBound := 3)) adaptive).run
      (((1, 2) : field × field),
        [((37, 0), (3 : field)), ((37, 1), 4), ((37, 1), 0)], ([], [])) =
    pure ((4 : field), ((1, 2) : field × field),
      [((37, 0), (3 : field)), ((37, 1), 4), ((37, 1), 0)],
      ([((37, 1), (4 : field)), ((37, 0), 3)], [((3, 37), (0 : field))])) := by
  simp only [adaptive, simulateQ_bind, simulateQ_spec_query, NativeHandler.goodSource,
    NativeHandler.source, StateT.run_bind]
  dsimp only [StateT.run]
  rw [Reply.goodHash_denote]
  simp only [BLS.LazyAGM.Reduction.privateListOracle_lookup, List.lookup_cons,
    beq_self_eq_true, map_pure, pure_bind, smul_eq_mul]
  rw [mul_one (3 : field)]
  rw [Reply.goodSign_denote, Index.oops_sourceTerms]
  rw [Model.LazyAGM.WeightedReduction.evalTerms_cached_eq _ _ (by
    intro p hp
    change p ∈ [((37, (0 : Fin 2)), (1 : field)), ((37, 1), 3)] at hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> exact ⟨_, rfl⟩)]
  rw [map_pure, pure_bind]
  rw [Reply.goodHash_denote, BLS.LazyAGM.Reduction.privateListOracle_lookup]
  rw [show OOPS.LazyAGM.terms 1 ((3, 37) : field × Nat) =
    [((37, (0 : Fin 2)), (1 : field)), ((37, 1), 3)] by decide]
  change (fun p : field × List ((Nat × Fin 2) × field) =>
    (p.1 • (1 : field), ((1, 2) : field × field), p.2,
      ([((37, 1), p.1 • (1 : field)), ((37, 0), (3 : field))],
        [((3, 37), (0 : field))]))) <$>
      pure ((4 : field), [((37, 0), (3 : field)), ((37, 1), 4), ((37, 1), 0)]) = _
  rw [map_pure]
  congr 1

end Native

open Lean Meta

run_meta do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let callers := #[``NativeHandler.goodCaller_bound, ``NativeHandler.badCaller_bound]
  let names := #[``store_encoded_size, ``goodStore_encoded_size, ``badStore_encoded_size,
    ``NativeHandler.handlerStoreWidth_ge, ``NativeHandler.reserved_empty,
    ``NativeHandler.reserved_weaken, ``NativeHandler.goodReserved_size,
    ``NativeHandler.badReserved_size, ``NativeHandler.goodHash_reserved,
    ``NativeHandler.goodSign_reserved, ``NativeHandler.badHash_reserved,
    ``NativeHandler.badSign_reserved, ``NativeHandler.goodCode_bound,
    ``NativeHandler.badCode_bound, ``NativeHandler.goodCode_description,
    ``NativeHandler.badCode_description, ``NativeHandler.goodCaller_description,
    ``NativeHandler.badCaller_description] ++ callers
  for name in names do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"
    forallTelescope (← getConstInfo name).type fun params _ => do
      for param in params do
        let type ← inferType param
        if type.isAppOf ``Finite || type.isAppOf ``Fintype then
          throwError "{name}: finite topic/slot/message domain required"
        if (type.find? (fun e => e.isConstOf ``Bounds)).isSome then
          throwError "{name}: supplied complete dispatcher/reply budget"
        if !callers.contains name &&
            (type.find? (fun e => e.isConstOf ``GeneralCaller.Budget)).isSome then
          throwError "{name}: supplied caller budget outside caller composition"

end SignaturesTest.WeightedOracleBudget
