import Signatures.Runtime.BackendWeightedOracle
import Signatures.Runtime.BackendWeightedReplyDescription
import Signatures.Runtime.BackendWeightedReplyCost
import Signatures.Runtime.BackendWeightedReplySize
import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

open OracleComp OracleSpec PFunctor
open Signatures.Runtime Signatures.Runtime.BackendProgram Signatures.Runtime.WeightedAGM

namespace SignaturesTest.WeightedReply

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private abbrev field := ZMod 5
private abbrev model := arithmetic field field field Nat Bool PrimitiveCosts.unit

section Native

variable {C : StepClass} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass C} [Q.HasCategory] [Q.HasProd] [Q.HasSum]
  {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase field field field Nat Bool))
  (data : DataCode Q rep.data) (sampling : MachineCompiler.SamplingImplementation Q iface rep)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) (model.execute instr))

-- Signing before any explicit hash uses the private cache without adding hash
-- tokens. Its one delivered signature is prepended to the existing signing log.
-- A shadowed binding and an unrelated cached key survive byte-for-byte at this view.
example : (Reply.goodSign rep data PrimitiveCosts.unit primitive sampling (.oops 1)).denote
    ((2, 37), ((1, 2) : field × field),
      [((37, 0), (3 : field)), ((37, 1), 4), ((37, 1), 0), ((99, 0), 2)],
      ([], [((1, 99), (4 : field))])) =
    pure ((2 : field), ((1, 2) : field × field),
      [((37, 0), (3 : field)), ((37, 1), 4), ((37, 1), 0), ((99, 0), 2)],
      ([], [((2, 37), (2 : field)), ((1, 99), 4)])) := by
  rw [Reply.goodSign_denote, Index.oops_sourceTerms]
  rw [Model.LazyAGM.WeightedReduction.evalTerms_cached_eq _ _ (by
    intro p hp
    change p ∈ [((37, (0 : Fin 2)), (1 : field)), ((37, 1), 2)] at hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> exact ⟨_, rfl⟩)]
  rw [map_pure]
  congr 1

-- A zero coefficient still reads its base. On a miss the new scalar is sampled
-- and retained, even though the delivered signature does not depend on it.
example : (Reply.goodSign rep data PrimitiveCosts.unit primitive sampling (.oops 1)).denote
    ((0, 37), ((1, 1) : field × field), [((37, 0), (2 : field))], ([], [])) =
      (fun rho : field => ((2 : field), ((1, 1) : field × field),
        [((37, (1 : Fin 2)), rho), ((37, 0), 2)], ([], [((0, 37), (2 : field))]))) <$>
          ($ᵗ field : ProbComp field) := by
  rw [Reply.goodSign_denote, Index.oops_sourceTerms]
  have ht : OOPS.LazyAGM.terms 1 ((0, 37) : field × Nat) =
      [((37, (0 : Fin 2)), (1 : field)), ((37, 1), 0)] := by decide
  rw [ht]
  simp [Model.LazyAGM.evalTerms, StateT.run_bind, bind_pure_comp, Reply.record]
  rfl

-- Paired masks evaluate both coordinates before the bad reduction's group
-- response. Proximity's constant coordinate is included even at message 0.
example : (Reply.badSign rep data PrimitiveCosts.unit primitive sampling (.proximity 1)).denote
    (((2, ()), 37), ((3, 1, 2) : field × field × field),
      [((0, 37), ((1, 2) : field × field)), ((1, 37), (3, 4)), ((1, 37), (0, 0))],
      ([((0, 37), (0 : field))], [])) =
    pure ((2 : field), ((3, 1, 2) : field × field × field),
      [((0, 37), ((1, 2) : field × field)), ((1, 37), (3, 4)), ((1, 37), (0, 0))],
      ([((0, 37), (0 : field))], [(((2, ()), 37), (2 : field))])) := by
  rw [Reply.badSign_denote, Index.proximity_sourceTerms]
  rw [Model.LazyAGM.WeightedReduction.evalTerms_cached_eq _ _ (by
    intro p hp
    change p ∈ [(((0 : Fin 2), 37), (1 : field)), ((1, 37), 2)] at hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> exact ⟨_, rfl⟩)]
  rw [map_pure]
  congr 1

-- Zero degree still signs the constant base and records one explicit reply.
example : (Reply.goodSign rep data PrimitiveCosts.unit primitive sampling (.oops 0)).denote
    ((0, 37), ((1, 2) : field × field), [((37, 0), (3 : field))], ([], [])) =
      pure ((1 : field), ((1, 2) : field × field), [((37, 0), (3 : field))],
        ([], [((0, 37), (1 : field))])) := by
  rw [Reply.goodSign_denote, Index.oops_sourceTerms]
  rw [Model.LazyAGM.WeightedReduction.evalTerms_cached_eq _ _ (by
    intro p hp
    change p ∈ [((37, (0 : Fin 1)), (1 : field))] at hp
    simp only [List.mem_singleton] at hp
    subst p
    exact ⟨_, rfl⟩)]
  rw [map_pure]
  congr 1

end Native

open Lean Meta

run_meta do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``Reply.chronological_record, ``Reply.replyResult_denote,
      ``Reply.signValue_denote, ``Reply.backendReply_denote,
      ``Reply.goodSignValue_source, ``Reply.badSignValue_source,
      ``Index.oops_sourceTerms, ``Index.proximity_sourceTerms,
      ``Reply.goodHash_denote, ``Reply.goodSign_denote, ``Reply.badHash_denote, ``Reply.badSign_denote,
      ``WeightedAGM.listSimulation, ``WeightedAGM.listRun,
      ``WeightedAGM.listHash_growth, ``WeightedAGM.listSign_growth,
      ``NativeHandler.goodSource_refines, ``NativeHandler.badSource_refines,
      ``NativeHandler.goodCaller_source, ``NativeHandler.badCaller_source,
      ``Reply.replyFrame_size, ``Reply.cacheArgs_size, ``Reply.replyResult_size,
      ``Reply.cacheArgs_cost, ``Reply.goodReplyResult_cost, ``Reply.badReplyResult_cost,
      ``Reply.signValue_description, ``Reply.backendReply_description,
      ``Reply.goodHash_description, ``Reply.goodSign_description,
      ``Reply.badHash_description, ``Reply.badSign_description] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"
    forallTelescope (← getConstInfo name).type fun params _ => do
      for param in params do
        let type ← inferType param
        if type.isAppOf ``Finite || type.isAppOf ``Fintype then
          throwError "{name}: finite topic/slot/message domain required"
        for forbidden in #[``Bounds, ``GeneralCaller.Budget] do
          if (type.find? (fun e => e.isConstOf forbidden)).isSome then
            throwError "{name}: supplied complete reply/solver budget"

end SignaturesTest.WeightedReply
