import Proofs.Runtime.BackendWeightedCache
import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

open OracleComp OracleSpec PFunctor Signatures.Runtime Signatures.Runtime.BackendProgram
open Signatures.Runtime.WeightedAGM Signatures.Runtime.WeightedAGM.PrivateCache

namespace SignaturesTest.WeightedCache

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private abbrev field := ZMod 5
private abbrev arithmeticModel := arithmetic field field field Nat Bool PrimitiveCosts.unit

variable {C : StepClass} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass C} [Q.HasCategory] [Q.HasProd] [Q.HasSum]
  {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase field field field Nat Bool))
  (data : DataCode Q rep.data) (sampling : MachineCompiler.SamplingImplementation Q iface rep)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) (arithmeticModel.execute instr))
  (store : C.Str (List Nat)) (saved : List Nat)

-- Infinite topics, a distinct message atom, shadowed keys, and cached zero.
-- The first matching full key wins; neither the default nor the later value
-- may replace zero, and looking past a different tag must not count as a hit.
example : (goodCache rep data sampling PrimitiveCosts.unit primitive store (.oops 3)).denote
    (((1000000, 1), 4, [((1000000, 0), 2), ((1000000, 1), 0), ((1000000, 1), 3)], ()), saved) =
      pure ((0, [((1000000, 0), 2), ((1000000, 1), 0), ((1000000, 1), 3)]), saved) := by
  exact StructuredCache.denote rep data ((Index.oops 3).code rep data PrimitiveCosts.unit primitive)
    store sampling.scalar (1000000, 1) 4 [((1000000, 0), 2), ((1000000, 1), 0), ((1000000, 1), 3)] saved

-- A new tag under the same topic is a miss and inserts exactly one entry.
example : (goodCache rep data sampling PrimitiveCosts.unit primitive store (.oops 3)).denote
    (((37, 2), 0, [((37, 1), 4)], ()), saved) =
      (fun v : field => ((v, [((37, 2), v), ((37, 1), 4)]), saved)) <$> ($ᵗ field) := by
  simp only [goodCache, access]
  rw [StructuredCache.denote (key := Weights.oopsKey 3) (val := scalar) rep data]
  change (fun v : field => ((v, [((37, 2), v), ((37, 1), 4)]), saved)) <$>
    sampling.scalar.denote () = _
  rw [sampling.scalar_denote]

-- A new topic at the same degree is also a miss.
example : (goodCache rep data sampling PrimitiveCosts.unit primitive store (.oops 3)).denote
    (((38, 1), 0, [((37, 1), 4)], ()), saved) =
      (fun v : field => ((v, [((38, 1), v), ((37, 1), 4)]), saved)) <$> ($ᵗ field) := by
  simp only [goodCache, access]
  rw [StructuredCache.denote (key := Weights.oopsKey 3) (val := scalar) rep data]
  change (fun v : field => ((v, [((38, 1), v), ((37, 1), 4)]), saved)) <$>
    sampling.scalar.denote () = _
  rw [sampling.scalar_denote]

-- Proximity compares both the constant/coordinate tag and the slot.
example : (badCache rep data sampling PrimitiveCosts.unit primitive store (.proximity 3)).denote
    (((0, 37), (4, 4), [((1, 37), (1, 2)), ((0, 38), (3, 4)), ((0, 37), (0, 0))], ()), saved) =
      pure (((0, 0), [((1, 37), (1, 2)), ((0, 38), (3, 4)), ((0, 37), (0, 0))]), saved) := by
  simp only [badCache, access]
  rw [StructuredCache.denote (key := Weights.proximityKey 3) (val := .pair scalar scalar) rep data]
  rfl

-- The bad branch samples a pair, not one scalar reused in both positions.
example : (badCache rep data sampling PrimitiveCosts.unit primitive store (.proximity 3)).denote
    (((2, 37), (0, 0), [((1, 37), (4, 3))], ()), saved) =
      (fun v : field × field => ((v, [((2, 37), v), ((1, 37), (4, 3))]), saved)) <$>
        ($ᵗ (field × field)) := by
  simp only [badCache, access]
  rw [StructuredCache.denote (key := Weights.proximityKey 3) (val := .pair scalar scalar) rep data]
  change (fun v : field × field => ((v, [((2, 37), v), ((1, 37), (4, 3))]), saved)) <$>
    (pairSampler rep data sampling).denote () = _
  rw [pairSampler_denote]

-- Degree and dimension zero retain their constant base and accept new labels.
example : (goodCache rep data sampling PrimitiveCosts.unit primitive store (.proximity 0)).denote
    (((0, 1000000), 0, [], ()), saved) =
      (fun v : field => ((v, [((0, 1000000), v)]), saved)) <$> ($ᵗ field) := by
  simp only [goodCache, access]
  rw [StructuredCache.denote (key := Weights.proximityKey 0) (val := scalar) rep data]
  change (fun v : field => ((v, [((0, 1000000), v)]), saved)) <$> sampling.scalar.denote () = _
  rw [sampling.scalar_denote]

example : (badCache rep data sampling PrimitiveCosts.unit primitive store (.oops 0)).denote
    (((37, 0), (0, 0), [], ()), saved) =
      (fun v : field × field => ((v, [((37, 0), v)]), saved)) <$> ($ᵗ (field × field)) := by
  simp only [badCache, access]
  rw [StructuredCache.denote (key := Weights.oopsKey 0) (val := .pair scalar scalar) rep data]
  change (fun v : field × field => ((v, [((37, 0), v)]), saved)) <$>
    (pairSampler rep data sampling).denote () = _
  rw [pairSampler_denote]

-- Cache reuse preserves even the costed run under sampler replacement. This
-- covers the no-fresh-randomness requirement during transcript extraction.
example (other : MachineCompiler.SamplingImplementation Q iface rep)
    (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat) :
    (goodCache rep data sampling PrimitiveCosts.unit primitive store (.oops 3)).run control queryCost
      (((37, 1), 4, [((37, 1), 0)], ()), saved) =
    (goodCache rep data other PrimitiveCosts.unit primitive store (.oops 3)).run control queryCost
      (((37, 1), 4, [((37, 1), 0)], ()), saved) :=
  goodCache_hit_run rep data sampling PrimitiveCosts.unit primitive store (.oops 3) other
    control queryCost (37, 1) 4 [((37, 1), 0)] saved 0 rfl

example (other : MachineCompiler.SamplingImplementation Q iface rep)
    (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat) :
    (badCache rep data sampling PrimitiveCosts.unit primitive store (.proximity 3)).run control queryCost
      (((0, 37), (4, 4), [((0, 37), (0, 0))], ()), saved) =
    (badCache rep data other PrimitiveCosts.unit primitive store (.proximity 3)).run control queryCost
      (((0, 37), (4, 4), [((0, 37), (0, 0))], ()), saved) :=
  badCache_hit_run rep data sampling PrimitiveCosts.unit primitive store (.proximity 3) other
    control queryCost (0, 37) (4, 4) [((0, 37), (0, 0))] saved (0, 0) rfl

-- The representation law starts from the original Option-valued coordinates,
-- and preserves the complete source cache even when a key occurs twice.
example (ell : Nat) (k : Option (Fin ell) × Nat)
    (cache : List ((Option (Fin ell) × Nat) × (field × field))) :
    (badCache rep data sampling PrimitiveCosts.unit primitive store (.proximity ell)).denote
      ((Weights.encodeProximityKey k, (0, 0), cache.map (Prod.map Weights.encodeProximityKey id), ()), saved) =
    (fun p => ((p.1, p.2.map (Prod.map Weights.encodeProximityKey id)), saved)) <$>
      ((BLS.LazyAGM.Reduction.privateListOracle (M := Option (Fin ell) × Nat) (R := field × field))
        (.inr k)).run cache :=
  proximity_badCache_denote rep data sampling PrimitiveCosts.unit primitive store ell k (0, 0) cache saved

-- A noninjective encoding would turn a fresh constant base into a cached
-- coordinate. The production encoding preserves their distinct tags.
example :
    let cache : List ((Option (Fin 3) × Nat) × field) := [((some 0, 37), 4)]
    cache.lookup (none, 37) = none ∧
      (cache.map (Prod.map Weights.encodeProximityKey id)).lookup (0, 37) = none ∧
      (cache.map (Prod.map (fun k => ((0 : Fin 4), k.2)) id)).lookup (0, 37) = some 4 := by
  decide

open Lean Meta

run_meta do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``Comparison.description, ``Comparison.cost,
      ``StructuredCache.lookup_encoded, ``StructuredCache.denote, ``StructuredCache.uniform,
      ``StructuredCache.uniform_encoded, ``StructuredCache.hit_run,
      ``StructuredCache.description, ``StructuredCache.bound,
      ``Index.expression_value, ``Index.description, ``Index.native_cost,
      ``pairSampler_denote, ``goodCache_denote, ``badCache_denote,
      ``proximity_goodCache_denote, ``proximity_badCache_denote,
      ``goodCache_hit_run, ``badCache_hit_run, ``access_bound,
      ``goodCache_bound, ``badCache_bound, ``goodCache_description, ``badCache_description] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"
  for name in #[``Index.code, ``Index.native_cost, ``goodCache, ``badCache,
      ``goodCache_denote, ``badCache_denote, ``proximity_goodCache_denote, ``proximity_badCache_denote,
      ``goodCache_bound, ``badCache_bound,
      ``goodCache_description, ``badCache_description] do
    forallTelescope (← getConstInfo name).type fun params _ => do
      for param in params do
        let declaration ← getFVarLocalDecl param
        let type := declaration.type
        if type.isAppOf ``Finite || type.isAppOf ``Fintype then
          throwError "{name}: weighted caches must permit infinite topic/slot domains"
        for forbidden in #[``Bounds, `Signatures.Runtime.GeneralCaller.Budget] do
          if type.find? (fun e => e.isConstOf forbidden) |>.isSome then
            throwError "{name}: cannot assume a finished cache/solver budget"
        if #[`comparison, `comparisonTime, `heq].contains declaration.userName then
          throwError "{name}: comparison implementation and cost must be derived"

end SignaturesTest.WeightedCache
