import Proofs.Runtime.BackendWeightedEvaluateDescription
import Proofs.Runtime.BackendWeightedReadBudget
import Proofs.Runtime.BackendWeightedGoodEvaluate
import Proofs.Runtime.BackendWeightedBadEvaluate
import Proofs.LinearFunctional.LazyAGMCache
import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

open OracleComp OracleSpec PFunctor Signatures.Runtime Signatures.Runtime.BackendProgram
open Signatures.Runtime.WeightedAGM Signatures.Runtime.WeightedAGM.Read
open Signatures.Runtime.WeightedAGM.Evaluate

namespace SignaturesTest.WeightedEvaluate

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private abbrev field := ZMod 5
private abbrev arithmeticModel := arithmetic field field field Nat Bool PrimitiveCosts.unit
private abbrev OopsIndex := Nat × Fin 4

private def loggedLookup (k : OopsIndex) : StateM (List OopsIndex) field :=
  fun seen => (if k.2.val = 0 then 2 else 3, seen ++ [k])

-- The first coefficient is zero, and the last key is repeated. All three
-- queries must still occur, in order, and the unrelated default is never read.
example : ((evaluateGood (indexTy := Weights.oopsKey 3)).denote arithmeticModel
    (evalSemantics loggedLookup) ([((37, 0), 0), ((37, 1), 2), ((37, 1), 4)], ((9999, 3), 4), ())).run [] =
      (3, [(37, 0), (37, 1), (37, 1)]) := by decide

example : ((evaluateGood (indexTy := Weights.oopsKey 3)).denote arithmeticModel
    (evalSemantics loggedLookup) ([], ((9999, 3), 4), ())).run [(8, 2)] = (0, [(8, 2)]) := by decide

private def pairLookup (k : Fin 4 × Nat) : StateM (List (Fin 4 × Nat)) (field × field) :=
  fun seen => ((if k.1.val = 0 then 2 else 3, if k.2 = 37 then 4 else 1), seen ++ [k])

-- Both pair coordinates are accumulated; constant and coordinate tags remain distinct.
example : ((evaluateBad (indexTy := Weights.proximityKey 3)).denote arithmeticModel
    (evalSemantics pairLookup) ([((0, 37), 2), ((1, 38), 4)], ((3, 9999), 0), ())).run [] =
      ((1, 2), [(0, 37), (1, 38)]) := by decide

section Compiled

variable {C : StepClass} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass C} [Q.HasCategory] [Q.HasProd] [Q.HasSum]
  {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase field field field Nat Bool))
  (data : DataCode Q rep.data) (sampling : MachineCompiler.SamplingImplementation Q iface rep)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) (arithmeticModel.execute instr))

example : (goodRead rep data PrimitiveCosts.unit primitive sampling (.oops 3)).denote
    ((37, 1), [((37, 0), 4), ((37, 1), 0), ((37, 1), 3)]) =
      pure (0, [((37, 0), 4), ((37, 1), 0), ((37, 1), 3)]) :=
  CacheRead.denote rep data ((Index.oops 3).code rep data PrimitiveCosts.unit primitive)
    (zeroCode rep data PrimitiveCosts.unit primitive (inputTy (Weights.oopsKey 3) scalar))
    sampling.scalar (37, 1) [((37, 0), 4), ((37, 1), 0), ((37, 1), 3)]

-- Empty evaluation preserves the cache and never uses the supplied default row.
example : (backendGood rep data PrimitiveCosts.unit primitive sampling (.oops 3)).denote
    (([], ((9999, 3), 4), ()), [((37, 0), 2)]) = pure (0, [((37, 0), 2)]) := by
  rw [backendGood_source]
  rfl

example : (backendBad rep data PrimitiveCosts.unit primitive sampling (.proximity 0)).denote
    (([], ((0, 9999), 4), ()), [((0, 37), (2, 4))]) = pure ((0, 0), [((0, 37), (2, 4))]) := by
  rw [backendBad_source]
  rfl

-- A zero-weight term on a missing key still samples and inserts a base.
example : (backendGood rep data PrimitiveCosts.unit primitive sampling (.oops 3)).denote
    (([((37, 1), 0)], ((9999, 3), 4), ()), []) =
      (fun v : field => (0, [((37, 1), v)])) <$> ($ᵗ field) := by
  rw [backendGood_source]
  simp only [Model.LazyAGM.evalTerms, simulateQ_bind, simulateQ_spec_query, simulateQ_pure,
    StateT.run_bind, StateT.run_pure]
  erw [BLS.LazyAGM.Reduction.privateListOracle_lookup]
  simp [List.lookup_nil, bind_pure_comp]

-- Repeated cached terms preserve the whole existing cache, including shadowed entries.
example : (backendGood rep data PrimitiveCosts.unit primitive sampling (.oops 3)).denote
    (([((37, 0), 0), ((37, 1), 2), ((37, 1), 4)], ((9999, 3), 4), ()),
      [((37, 0), 2), ((37, 1), 3), ((37, 1), 4)]) =
        pure (3, [((37, 0), 2), ((37, 1), 3), ((37, 1), 4)]) := by
  rw [backendGood_source]
  rw [Model.LazyAGM.WeightedReduction.evalTerms_cached_eq _ _ (by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    all_goals exact ⟨_, rfl⟩)]
  rfl

example (other : MachineCompiler.SamplingImplementation Q iface rep)
    (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat) :
    (badRead rep data PrimitiveCosts.unit primitive sampling (.proximity 3)).run control queryCost
      ((0, 37), [((0, 37), (0, 0))]) =
    (badRead rep data PrimitiveCosts.unit primitive other (.proximity 3)).run control queryCost
      ((0, 37), [((0, 37), (0, 0))]) :=
  badRead_hit_run rep data PrimitiveCosts.unit primitive sampling (.proximity 3) other
    control queryCost (0, 37) [((0, 37), (0, 0))] (0, 0) rfl

end Compiled

open Lean Meta

run_meta do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``CacheRead.denote, ``CacheRead.uniform, ``CacheRead.hit_run, ``CacheRead.description, ``CacheRead.bound,
      ``goodRead_denote, ``badRead_denote, ``goodRead_hit_run, ``badRead_hit_run,
      ``zeroCode_cost, ``pairZeroCode_cost, ``goodRead_bound, ``badRead_bound,
      ``zeroCode_description, ``pairZeroCode_description, ``goodRead_description, ``badRead_description,
      ``selectRow_denote, ``evalUpdate_denote, ``evalBody_denote, ``evaluateRows_denote,
      ``foldTerms_simulate, ``evaluateRows_source, ``evaluateGood_source, ``evaluateBad_source,
      ``backendEvaluate_source, ``backendGood_source, ``backendBad_source,
      ``backendEvaluate_description, ``backendGood_description, ``backendBad_description,
      ``compileRead_denote, ``evalBody_source, ``backendRead_state, ``evalBody_state, ``evalBody_remaining,
      ``evaluationRow_key_size, ``evaluationSelected_size, ``evaluationRows_size, ``evaluationFrame_size,
      ``evaluationUpdateFrame_size, ``evaluationCache_size, ``selectRow_time_bound,
      ``goodUpdate_time_bound, ``badUpdate_time_bound, ``evalKey_cost, ``evalBody_bound,
      ``evaluateInit_cost, ``backendEvaluate_bound, ``goodBody_budget, ``badBody_budget,
      ``backendGood_bound, ``backendBad_bound] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"
  for name in #[``goodRead, ``badRead, ``goodRead_bound, ``badRead_bound,
      ``goodRead_description, ``badRead_description, ``backendGood, ``backendBad,
      ``backendGood_source, ``backendBad_source, ``backendGood_description, ``backendBad_description,
      ``goodBody_budget, ``badBody_budget, ``backendGood_bound, ``backendBad_bound] do
    forallTelescope (← getConstInfo name).type fun params _ => do
      for param in params do
        let declaration ← getFVarLocalDecl param
        let type := declaration.type
        if type.isAppOf ``Finite || type.isAppOf ``Fintype then
          throwError "{name}: finite topic/slot domains are not required"
        for forbidden in #[``Bounds, `Signatures.Runtime.GeneralCaller.Budget] do
          if type.find? (fun e => e.isConstOf forbidden) |>.isSome then
            throwError "{name}: cannot assume a completed read/evaluator budget"
        if #[`reader, `hreader, `comparison, `hcomparison, `hread, `hbody, `inv, `hcount, `hinit].contains declaration.userName then
          throwError "{name}: reader, body, and loop budgets must be derived from primitive contracts"

end SignaturesTest.WeightedEvaluate
