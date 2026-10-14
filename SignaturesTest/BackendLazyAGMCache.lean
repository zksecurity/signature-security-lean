import Signatures.Runtime.BackendLazyAGMCache
import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

open OracleComp OracleSpec PFunctor Signatures.Runtime Signatures.Runtime.BackendProgram

namespace SignaturesTest.BackendLazyAGMCache

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

section Execution

variable {C : StepClass} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass C} [Q.HasCategory] [Q.HasProd] [Q.HasSum]
  {S : Type} {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase (ZMod 5) (ZMod 5) (ZMod 5) Nat Nat))
  (data : DataCode Q rep.data) (sampling other : MachineCompiler.SamplingImplementation Q iface rep)
  (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic (ZMod 5) (ZMod 5) (ZMod 5) Nat Nat cost).execute instr))
  (store : C.Str S) (saved : S)

-- A zero is a cached value; the first binding wins over the later nonzero one.
-- Replacing every primitive sampler preserves the entire native run, including time.
example (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat) :
    (LazyAGM.goodCache rep data sampling cost primitive store).run control queryCost
      ((7, 4, [(7, 0), (7, 3)], ()), saved) =
    (LazyAGM.goodCache rep data other cost primitive store).run control queryCost
      ((7, 4, [(7, 0), (7, 3)], ()), saved) := by
  apply LazyAGM.goodCache_hit_run
  rfl

example (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat) :
    (LazyAGM.badCache rep data sampling cost primitive store).run control queryCost
      ((7, (4, 4), [(7, (0, 0)), (7, (2, 3))], ()), saved) =
    (LazyAGM.badCache rep data other cost primitive store).run control queryCost
      ((7, (4, 4), [(7, (0, 0)), (7, (2, 3))], ()), saved) := by
  apply LazyAGM.badCache_hit_run
  rfl

-- The supplied default pair does not leak into a miss. There are two independent
-- scalar draws, one new entry, and no change to the unrelated ambient store.
example : (LazyAGM.badCache rep data sampling cost primitive store).denote
    ((99, (4, 4), [], ()), saved) = (do
      let a ← ($ᵗ (ZMod 5) : ProbComp (ZMod 5))
      let b ← ($ᵗ (ZMod 5) : ProbComp (ZMod 5))
      pure (((a, b), [(99, (a, b))]), saved)) := by
  rw [LazyAGM.badCache_denote, BLS.LazyAGM.Reduction.privateListOracle_lookup]
  simp only [List.lookup_nil, Functor.map_map]
  change (fun p : ZMod 5 × ZMod 5 => ((p, [(99, p)]), saved)) <$>
    ((Prod.mk <$> ($ᵗ (ZMod 5) : ProbComp (ZMod 5))) <*> ($ᵗ (ZMod 5) : ProbComp (ZMod 5))) = _
  simp [seq_eq_bind_map, bind_map_left, map_bind, bind_pure_comp]

example : (LazyAGM.badCache rep data sampling cost primitive store).denote
    ((7, (4, 4), [(7, (0, 0)), (7, (2, 3))], ()), saved) =
      pure (((0, 0), [(7, (0, 0)), (7, (2, 3))]), saved) := by
  rw [LazyAGM.badCache_denote, BLS.LazyAGM.Reduction.privateListOracle_lookup]
  rfl

end Execution

open Lean Meta Elab Command

run_cmd liftTermElabM do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``PairSampling.denote, ``PairSampling.uniform, ``PairSampling.bound,
      ``PairSampling.description, ``SampledCache.lookupValue_lookup,
      ``SampledCache.denote, ``SampledCache.uniform, ``SampledCache.hit_run,
      ``SampledCache.bound, ``SampledCache.description, ``LazyAGM.pairSampler_denote,
      ``LazyAGM.goodCache_denote, ``LazyAGM.badCache_denote,
      ``LazyAGM.goodCache_hit_run, ``LazyAGM.badCache_hit_run,
      ``LazyAGM.goodCache_bound, ``LazyAGM.badCache_bound,
      ``LazyAGM.goodCache_description, ``LazyAGM.badCache_description] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"
  for name in #[``LazyAGM.goodCache, ``LazyAGM.badCache,
      ``LazyAGM.goodCache_denote, ``LazyAGM.badCache_denote,
      ``LazyAGM.goodCache_bound, ``LazyAGM.badCache_bound,
      ``LazyAGM.goodCache_description, ``LazyAGM.badCache_description] do
    forallTelescope (← getConstInfo name).type fun params _ => do
      for param in params do
        let type ← inferType param
        if type.isAppOf ``Finite || type.isAppOf ``Fintype then
          if let .fvar id := type.getAppArgs[0]! then
            if (← id.getUserName) == `M then
              throwError "{name}: finite-message premise added to a native lazy cache"

end SignaturesTest.BackendLazyAGMCache
