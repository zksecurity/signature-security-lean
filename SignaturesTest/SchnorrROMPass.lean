import Proofs.Runtime.BackendSchnorrROMPassSource
import Proofs.Runtime.BackendSchnorrROMPassDescription
import Proofs.Runtime.BackendSchnorrROMPassPolynomial
import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

/-! Final-pass regressions: use the live cache, preserve replay ordering, and
skip the final sampler completely on cutoff. General source laws must keep
arbitrary message types and require no default message or finite-domain bound. -/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation
open Signatures.Runtime Signatures.Runtime.BackendProgram
open Signatures.Runtime.Schnorr ListROM

namespace SignaturesTest.SchnorrROMPass

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private abbrev F := ZMod 5

section Execution

variable {C : StepClass} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass C} [Q.HasCategory] [Q.HasProd] [Q.HasSum] [Q.IsDistributive]
  [Q.HasOption] [OptionCode (Q := Q)] {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F F F Nat Nat))
  (bd : Boundary C (NativeInterface.sourceSpec F F Nat).toPFunctor F (Nat × F × F))
  (boundary : NativePass.DataPorts (Q := Q) rep bd)
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F F F Nat Nat cost).execute instr))
  (sampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))

/-- Final verification retains both caches, but uses the conflicting live value. -/
example :
    (NativePass.terminal rep bd boundary data cost primitive sampler).denote
      (some (7, 3, 0), ((1, 2), [((7, 3), 0)], [((7, 3), 2)]), [], [(1, 4, 0)]) =
      pure ([(((7, 3, 0), 2), ((1, 2), [((7, 3), 0)], [((7, 3), 2)]))], [], [(1, 4, 0)]) := by
  rw [NativePass.terminal_denote]
  dsimp only
  rw [NativeComponents.finalHash_denote, NativeCache.live_denote]
  simp only [cacheMap, ↓reduceIte, map_pure]

/-- Equality of complete costed runs, even when the inactive samplers differ. -/
example (other : Code Q unifSpec iface rep.data.unit (rep.ty scalar))
    (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
    (saved : Shared.Store F F Nat) :
    (NativePass.terminal rep bd boundary data cost primitive sampler).run control queryCost (none, saved) =
      (NativePass.terminal rep bd boundary data cost primitive other).run control queryCost (none, saved) := by
  simp only [NativePass.terminal, Code.run, sequenceRun, retainRun, chargeRun,
    pure_bind, map_pure, NativePass.optionView, Sum.elim_inl]

variable (sample : sampler.denote () = ($ᵗ F : ProbComp F))
  (ports : NativeInterface.Ports (Q := Q) rep bd)
  (uniform : UniformSampling.Ports (Q := Q) rep.data (iface := iface))
  (privatePorts : RawTape.NativePrivate.Ports (Q := Q) rep (iface := iface))
  (R : GeneralCaller.Caller (Q := Q) (bd := bd))

/-- A zero-query attacker still performs the final live query. Private cells
remain in order around the replayed challenge cell. -/
example (hreturn : R.machine.view (R.machine.init 2) = .inl (7, 3, 0)) :
    (NativePass.code rep bd boundary data cost primitive sampler ports uniform privatePorts R 0).denote
      (([], [(3, 0, 1), (1, 2, 0), (3, 0, 0)]), 1, 2) =
      pure ([(((7, 3, 0), 2), ((1, 2), [], [((7, 3), 2)]))], [], [(3, 0, 1), (3, 0, 0)]) := by
  rw [NativePass.code_denote,
    NativeHandler.caller_denote rep bd ports data cost primitive uniform privatePorts sampler sample R,
    runWithInput, runWith_return R.machine _ 0 _ _ hreturn, StateT.run_pure, pure_bind,
    NativePass.terminal_denote]
  dsimp only
  rw [NativeComponents.finalHash_denote, NativeCache.live_denote]
  simp only [cacheMap]
  have hd : (NativeDraw.challenge rep data cost primitive sampler).denote
      ((), [], [(3, 0, 1), (1, 2, 0), (3, 0, 0)]) = pure (2, [], [(3, 0, 1), (3, 0, 0)]) :=
    NativeDraw.challenge_denote rep data cost primitive sampler
      (⟨[], [(3, 0, 1), (1, 2, 0), (3, 0, 0)]⟩ : RawTape.State F)
  rw [hd]
  rfl

end Execution

open Lean Meta in
run_meta do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``NativePass.setup_denote, ``NativePass.verify_denote, ``NativePass.finishSome_denote,
      ``NativePass.cutoff_denote, ``NativePass.terminal_denote, ``NativePass.code_denote,
      ``NativePass.source, ``NativePass.source_of_resources, ``NativePass.completed_of_resources,
      ``NativePass.setup_description, ``NativePass.verify_description, ``NativePass.finishSome_description,
      ``NativePass.cutoff_description, ``NativePass.terminal_description, ``NativePass.code_description,
      ``NativePass.initialExpression_cost, ``NativePass.verifyInput_cost, ``NativePass.verifyOutput_cost,
      ``NativePass.singletonExpression_cost, ``NativePass.cutoffExpression_cost,
      ``NativePass.initial_reserved, ``NativePass.completed_size, ``NativePass.verified_size,
      ``NativePass.result_size, ``NativePass.verify_bound_of_finalHash,
      ``NativePass.setup_bound, ``NativePass.terminal_bound_of_verification, ``NativePass.code_bound_of_resources,
      ``NativePass.frameWidth_polynomial, ``NativePass.finalHashTime_polynomial,
      ``NativePass.timeBudget_polynomial, ``NativePass.resourcesTime_polynomial] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"
  for name in #[``NativePass.source_of_resources, ``NativePass.completed_of_resources] do
    forallTelescope (← getConstInfo name).type fun params conclusion => do
      let mut measured := false
      for param in params do
        let type ← inferType param
        if (type.find? (fun e => e.isConstOf ``QuantitativeRealization.RunsWithin)).isSome then
          measured := true
        for forbidden in #[``Bounds, ``Program, ``SourceCertificate, ``Fintype, ``Finite, ``Inhabited] do
          if (type.find? (fun e => e.isConstOf forbidden)).isSome then
            throwError "{name}: preserve arbitrary callers/messages without a default or finished budget"
        let userName := (← getFVarLocalDecl param).userName
        if #[`arityCap, `counterCap, `domainSize, `valid, `defaultMessage].contains userName then
          throwError "{name}: source correspondence must cover every supplied raw tape"
      unless measured do
        throwError "derive pass completion from measured query resources"
      if name == ``NativePass.source_of_resources then
        unless conclusion.isAppOf ``Eq &&
            (conclusion.find? (fun e => e.isConstOf ``NativePass.code)).isSome do
          throwError "require exact computation equality for the actual assembled pass"
  forallTelescope (← getConstInfo ``NativePass.code_bound_of_resources).type fun params conclusion => do
    let mut measured := false
    let mut sampled := false
    let mut ports := false
    for param in params do
      let type ← inferType param
      if (type.find? (fun e => e.isConstOf ``QuantitativeRealization.RunsWithin)).isSome then
        measured := true
      if (type.find? (fun e => e.isConstOf ``ExecutionProfile.Within)).isSome then
        sampled := true
      if (type.find? (fun e => e.isConstOf ``NativePass.PortCaps)).isSome then
        ports := true
      for forbidden in #[``Bounds, ``GeneralCaller.Budget, ``Program, ``SourceCertificate,
          ``Fintype, ``Finite, ``Inhabited, ``Expression.compile, ``Expression.compileBound] do
        if (type.find? (fun e => e.isConstOf forbidden)).isSome then
          throwError "derive the complete pass budget from arbitrary measured callers and local contracts"
      let name := (← getFVarLocalDecl param).userName
      if #[`callerInv, `hcallerStep, `hcallerWidth, `hhandler, `hbudget, `hverify, `hfinal, `valid].contains name then
        throwError "discharge completed pass components and cover all bounded replay tapes"
    unless measured && sampled && ports do
      throwError "require actual caller resources, original sampler resources and actual boundary contracts"
    unless conclusion.isAppOf ``Bounds &&
        (conclusion.find? (fun e => e.isConstOf ``NativePass.code)).isSome &&
        (conclusion.find? (fun e => e.isConstOf ``NativePass.ResultBound)).isSome do
      throwError "certify the entire actual pass with complete output and tape invariants"
  for name in #[``NativePass.finalHashTime_polynomial, ``NativePass.resourcesTime_polynomial] do
    forallTelescope (← getConstInfo name).type fun params _ => do
      for param in params do
        let userName := (← getFVarLocalDecl param).userName
        if #[`arityCap, `counter, `counterCap, `domainSize, `hCaller, `hHash, `hPass].contains userName then
          throwError "derive polynomial pass runtime without completed-budget or numeric-domain premises"

end SignaturesTest.SchnorrROMPass
