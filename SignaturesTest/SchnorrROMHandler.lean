import Signatures.Runtime.BackendSchnorrROMHandlerDescription
import Signatures.Runtime.BackendSchnorrROMHandlerPrimitiveBudget
import Signatures.Runtime.BackendSchnorrRawFork
import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

/-! Shared-state execution regressions and source/description theorem guards.
The actual backend adapters must preserve configuration, both distinct caches,
and the ordering of private and challenge cells. -/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation
open Signatures.Runtime Signatures.Runtime.BackendProgram
open Signatures.Runtime.Schnorr
open ListROM

namespace SignaturesTest.SchnorrROMHandler

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private abbrev F := ZMod 5

section Execution

variable {C : StepClass} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass C} [Q.HasCategory] [Q.HasProd] [Q.HasSum] [Q.IsDistributive]
  {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F F F Nat Nat))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F F F Nat Nat cost).execute instr))
  (sampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))

/-- Replay inserts into both caches without changing config, the saved prefix,
or the two interleaved private replies. -/
example :
    (NativeComponents.hash rep data cost primitive sampler).denote
      ((7, 3), ((1, 2), [], []), [(3, 0, 1)], [(3, 0, 0), (1, 4, 0), (3, 0, 1)]) =
      pure (4, ((1, 2), [((7, 3), 4)], [((7, 3), 4)]),
        [(3, 0, 1)], [(3, 0, 0), (3, 0, 1)]) := by
  rw [NativeComponents.hash_denote, NativeCache.managed_denote]
  simp only [cacheMap]
  rw [NativeCache.live_denote]
  simp only [cacheMap]
  have hd : (NativeDraw.challenge rep data cost primitive sampler).denote
      ((), [(3, 0, 1)], [(3, 0, 0), (1, 4, 0), (3, 0, 1)]) =
      pure (4, [(3, 0, 1)], [(3, 0, 0), (3, 0, 1)]) :=
    NativeDraw.challenge_denote rep data cost primitive sampler
      (⟨[(3, 0, 1)], [(3, 0, 0), (1, 4, 0), (3, 0, 1)]⟩ : RawTape.State F)
  rw [hd]
  rfl

/-- Ordinary hashing returns the managed cached zero. -/
example :
    (NativeComponents.hash rep data cost primitive sampler).denote
      ((7, 3), ((1, 2), [((7, 3), 0)], [((7, 3), 2)]), [], [(1, 4, 0)]) =
      pure (0, ((1, 2), [((7, 3), 0)], [((7, 3), 2)]), [], [(1, 4, 0)]) := by
  rw [NativeComponents.hash_denote, NativeCache.managed_denote]
  simp only [cacheMap, ↓reduceIte, map_pure]

/-- Final verification uses the live cache, even when the managed cache and
replay tape disagree with it. -/
example :
    (NativeComponents.finalHash rep data cost primitive sampler).denote
      ((7, 3), ((1, 2), [((7, 3), 0)], [((7, 3), 2)]), [], [(1, 4, 0)]) =
      pure (2, ((1, 2), [((7, 3), 0)], [((7, 3), 2)]), [], [(1, 4, 0)]) := by
  rw [NativeComponents.finalHash_denote, NativeCache.live_denote]
  simp only [cacheMap, ↓reduceIte, map_pure]

variable (uniform : UniformSampling.Ports (Q := Q) rep.data (iface := iface))
  (privatePorts : RawTape.NativePrivate.Ports (Q := Q) rep (iface := iface))

private def bitValue : Expr CryptoOp [.nat] scalar :=
  .branch (.op .natEq (.pair (.var .here) (.nat 0))) (.op .zero .unit) (.op .one .unit)

private def bitSampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar) :=
  .seq (.atomic (data.nat 1)) (.seq (UniformSampling.code rep.data uniform)
    (.atomic (RawTape.NativeFork.compileLocal rep data cost primitive bitValue)))

/-- Signing consumes both private draws in order and preserves the live cache,
including a conflicting value at the point just programmed into managed state. -/
example :
    (NativeComponents.signing rep data cost primitive uniform privatePorts
      (bitSampler rep data cost primitive uniform)).denote
      (7, ((1, 2), [], [((7, 3), 4)]), [], [(3, 0, 1), (1, 4, 0), (3, 0, 0), (3, 0, 1)]) =
      pure ((3, 0), ((1, 2), [((7, 3), 1)], [((7, 3), 4)]), [], [(1, 4, 0), (3, 0, 1)]) := by
  have first :
      (RawTape.NativePrivate.code rep data cost primitive uniform privatePorts
        (bitSampler rep data cost primitive uniform)).denote
        ((), [], [(3, 0, 1), (1, 4, 0), (3, 0, 0), (3, 0, 1)]) =
        pure (1, [], [(1, 4, 0), (3, 0, 0), (3, 0, 1)]) := by
    refine (RawTape.NativePrivate.source rep data cost primitive uniform privatePorts
      (bitSampler rep data cost primitive uniform) ()
      (⟨[], [(3, 0, 1), (1, 4, 0), (3, 0, 0), (3, 0, 1)]⟩ : RawTape.State F)).trans ?_
    simp only [bitSampler, Code.denote, UniformSampling.denote]
    rfl
  have second :
      (RawTape.NativePrivate.code rep data cost primitive uniform privatePorts
        (bitSampler rep data cost primitive uniform)).denote
        ((), [], [(1, 4, 0), (3, 0, 0), (3, 0, 1)]) =
        pure (0, [], [(1, 4, 0), (3, 0, 1)]) := by
    refine (RawTape.NativePrivate.source rep data cost primitive uniform privatePorts
      (bitSampler rep data cost primitive uniform) ()
      (⟨[], [(1, 4, 0), (3, 0, 0), (3, 0, 1)]⟩ : RawTape.State F)).trans ?_
    simp only [bitSampler, Code.denote, UniformSampling.denote]
    rfl
  rw [NativeComponents.signing_denote, NativeCache.signing_denote, first, pure_bind, second, pure_bind]
  norm_num
  rw [← Expr.run_value, cacheProgram_value _ _ (hashEq_value cost), lookupValue_cacheMap]
  decide

variable {Input Output : Type}
  (bd : Boundary C (NativeInterface.sourceSpec F F Nat).toPFunctor Input Output)
  (ports : NativeInterface.Ports (Q := Q) rep bd)

/-- The executed dispatcher produces a correctly typed reply even for malformed
raw tape naturals, preserving both caches and unrelated tape cells. -/
example :
    (NativeHandler.code rep bd ports data cost primitive uniform privatePorts sampler).denote
      (.inl (.inl 2), ((1, 2), [((7, 3), 0)], [((7, 3), 4)]),
        [(3, 0, 1)], [(1, 4, 0), (4, 0, 8), (3, 0, 0)]) =
      pure ((⟨.inl (.inl 2), (2 : Fin 3)⟩ : NativeInterface.Response F F Nat),
        ((1, 2), [((7, 3), 0)], [((7, 3), 4)]), [(3, 0, 1)], [(1, 4, 0), (3, 0, 0)]) := by
  simp only [NativeHandler.code, NativeHandler.dispatch, NativeHandler.inner,
    Code.denote, map_pure, pure_bind, id_eq, Sum.elim]
  rw [NativeHandler.random, NativeHandler.tagged_denote, NativeComponents.random_denote]
  have hd : (RawTape.NativeUniform.code rep data cost primitive uniform).denote
      (2, [(3, 0, 1)], [(1, 4, 0), (4, 0, 8), (3, 0, 0)]) =
      pure (8, [(3, 0, 1)], [(1, 4, 0), (3, 0, 0)]) :=
    RawTape.NativeUniform.denote rep data cost primitive uniform 2
      (⟨[(3, 0, 1)], [(1, 4, 0), (4, 0, 8), (3, 0, 0)]⟩ : RawTape.State F)
  rw [hd]
  rfl

end Execution

open Lean Meta in
run_meta do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``Shared.interpret_simulate, ``NativeComponents.hash_source,
      ``NativeComponents.signing_source, ``NativeComponents.finalHash_source,
      ``NativeComponents.random_source, ``NativeHandler.code_denote,
      ``NativeHandler.executed_erase, ``NativeHandler.caller_source_of_resources,
      ``NativeHandler.caller_no_cutoff_of_resources, ``NativeHandler.code_description,
      ``NativeHandler.finalHash_description, ``NativeHandler.caller_description,
      ``Bounds.time_mono, ``NativeComponents.randomInput_cost, ``NativeComponents.randomOutput_cost,
      ``NativeComponents.hashInput_cost, ``NativeComponents.hashOutput_cost,
      ``NativeComponents.signingInput_cost, ``NativeComponents.signingOutput_cost,
      ``NativeComponents.finalInput_cost, ``NativeComponents.finalOutput_cost,
      ``NativeComponents.store_mono, ``NativeComponents.store_size, ``NativeComponents.input_size,
      ``NativeComponents.hash_bound_of_native, ``NativeComponents.finalHash_bound_of_native,
      ``NativeComponents.signing_bound_of_native, ``NativeComponents.random_bound_of_native,
      ``NativeComponents.cache_components_bound, ``NativeComponents.random_bound,
      ``NativeComponents.cache_components_polynomial, ``NativeComponents.randomTime_polynomial] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"
  for name in #[``NativeHandler.code_denote, ``NativeHandler.caller_source_of_resources] do
    forallTelescope (← getConstInfo name).type fun params conclusion => do
      unless conclusion.isAppOf ``Eq do
        throwError "{name}: require exact source computation equality"
      for param in params do
        let type ← inferType param
        for forbidden in #[``Bounds, ``Program, ``SourceCertificate, ``Fintype, ``Finite] do
          if (type.find? (fun e => e.isConstOf forbidden)).isSome then
            throwError "{name}: no finished efficiency, arithmetic-attacker or finite-domain premise"
        let userName := (← getFVarLocalDecl param).userName
        if #[`arityCap, `counterCap, `domainSize, `valid].contains userName then
          throwError "{name}: cover all tape states and dynamically requested arities"
      if name == ``NativeHandler.caller_source_of_resources then
        let mut measured := false
        for param in params do
          let type ← inferType param
          if (type.find? (fun e => e.isConstOf ``QuantitativeRealization.RunsWithin)).isSome then
            measured := true
        unless measured do
          throwError "derive caller termination from measured resources"
  for name in #[``NativeComponents.cache_components_bound, ``NativeComponents.random_bound] do
    forallTelescope (← getConstInfo name).type fun params conclusion => do
      let mut profile := false
      for param in params do
        let type ← inferType param
        if (type.find? (fun e => e.isConstOf ``ExecutionProfile.Within)).isSome then
          profile := true
        for forbidden in #[``Bounds, ``Program, ``SourceCertificate, ``Fintype, ``Finite,
            ``Expression.compile, ``Expression.compileBound] do
          if (type.find? (fun e => e.isConstOf forbidden)).isSome then
            throwError "{name}: derive complete shared-store component budgets from primitive/original resources"
      if name == ``NativeComponents.cache_components_bound then
        unless profile do
          throwError "recover both scalar sampler budgets from the original execution profile"
        let conclusion ← whnf conclusion
        unless conclusion.isAppOf ``And && conclusion.getAppArgs[1]!.isAppOf ``And do
          throwError "certify final-live-hash, managed hash and signing together"
        let bounds := #[conclusion.getAppArgs[0]!, conclusion.getAppArgs[1]!.getAppArgs[0]!,
          conclusion.getAppArgs[1]!.getAppArgs[1]!]
        for (bound, component) in bounds.zip #[``NativeComponents.finalHash, ``NativeComponents.hash, ``NativeComponents.signing] do
          unless bound.isAppOf ``Bounds && (bound.find? (fun e => e.isConstOf component)).isSome do
            throwError "certify the actual shared-store {component} program"
      else
        unless conclusion.isAppOf ``Bounds &&
            (conclusion.find? (fun e => e.isConstOf ``NativeComponents.random)).isSome do
          throwError "certify the actual shared-store private-draw program"
  for name in #[``NativeComponents.cache_components_polynomial, ``NativeComponents.randomTime_polynomial] do
    forallTelescope (← getConstInfo name).type fun params _ => do
      for param in params do
        let userName := (← getFVarLocalDecl param).userName
        if #[`arityCap, `counter, `counterCap, `domainSize].contains userName then
          throwError "{name}: no polynomial numeric-arity/counter or finite-domain assumption"

end SignaturesTest.SchnorrROMHandler
