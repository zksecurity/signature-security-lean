import Signatures.Runtime.BackendSchnorrROMCallerOutput
import Signatures.Runtime.BackendSchnorrROMCallerPolynomial
import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

/-! Scope and boundary regressions for arbitrary ROM caller composition. A
zero-fuel readout must retain a finished output but must not execute a pending
request. The full runtime endpoint must derive its handler and caller budgets. -/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation
open Signatures.Runtime Signatures.Runtime.BackendProgram
open Signatures.Runtime.Schnorr ListROM

namespace SignaturesTest.SchnorrROMCaller

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private abbrev F := ZMod 5

example : NativeHandler.kind (G := F) (M := Nat) (.inl (.inl (2 ^ 64))) = 0 := rfl
example : NativeHandler.kind (G := F) (M := Nat) (.inl (.inr (7, 3))) = 1 := rfl
example : NativeHandler.kind (G := F) (M := Nat) (.inr 7) = 2 := rfl

section Boundary

variable {C : StepClass} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass C} [Q.HasCategory] [Q.HasProd] [Q.HasSum] [Q.IsDistributive]
  [Q.HasOption] [OptionCode (Q := Q)] {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F F F Nat Nat))
  (bd : Boundary C (NativeInterface.sourceSpec F F Nat).toPFunctor Nat Nat)
  (ports : NativeInterface.Ports (Q := Q) rep bd)
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F F F Nat Nat cost).execute instr))
  (uniform : UniformSampling.Ports (Q := Q) rep.data (iface := iface))
  (privatePorts : RawTape.NativePrivate.Ports (Q := Q) rep (iface := iface))
  (sampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))
  (sample : sampler.denote () = ($ᵗ F : ProbComp F))
  (R : GeneralCaller.Caller (Q := Q) (bd := bd))

example (input out : Nat) (saved : Shared.Store F F Nat)
    (hreturn : R.machine.view (R.machine.init input) = .inl out) :
    (NativeHandler.caller rep bd ports data cost primitive uniform privatePorts sampler R 0).denote (input, saved) =
      pure (some out, saved) := by
  rw [NativeHandler.caller_denote rep bd ports data cost primitive uniform privatePorts sampler sample R]
  rw [runWithInput, runWith_return R.machine _ 0 _ out hreturn]
  rfl

/-- Cutoff must preserve the complete initial store without drawing randomness. -/
example (input : Nat) (saved : Shared.Store F F Nat)
    (next : Fin (2 ^ 64 + 1) → R.machine.State)
    (hquery : R.machine.view (R.machine.init input) = .inr ⟨.inl (.inl (2 ^ 64)), next⟩) :
    (NativeHandler.caller rep bd ports data cost primitive uniform privatePorts sampler R 0).denote (input, saved) =
      pure (none, saved) := by
  rw [NativeHandler.caller_denote rep bd ports data cost primitive uniform privatePorts sampler sample R]
  rw [runWithInput, runWith_query_zero R.machine _ _ (.inl (.inl (2 ^ 64))) next hquery]
  rfl

end Boundary

open Lean Meta in
run_meta do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``NativeHandler.requestBound_mono, ``NativeHandler.requestBound_of_size,
      ``NativeHandler.recovery_of_encoding, ``NativeHandler.canonicalRecovery,
      ``NativeHandler.executed_mem_code, ``NativeHandler.caller_bound_of_handler,
      ``NativeHandler.caller_bound, ``NativeHandler.reachable_request, ``NativeHandler.reachable_output,
      ``NativeHandler.resource_step, ``NativeHandler.caller_bound_of_resources,
      ``NativeHandler.caller_reference_denote, ``NativeHandler.caller_output_invariant,
      ``NativeHandler.caller_output_size_of_resources,
      ``NativeHandler.callerTime_polynomial, ``NativeHandler.callerResourcesTime_polynomial] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"
  for name in #[``NativeHandler.caller_bound_of_resources, ``NativeHandler.caller_output_size_of_resources] do
    forallTelescope (← getConstInfo name).type fun params _ => do
      let mut measured := false
      let mut actual := false
      let mut sampler := false
      for param in params do
        let type ← inferType param
        if (type.find? (fun e => e.isConstOf ``QuantitativeRealization.RunsWithin)).isSome then
          measured := true
        if (type.find? (fun e => e.isConstOf ``NativeHandler.caller)).isSome then
          actual := true
        if (type.find? (fun e => e.isConstOf ``ExecutionProfile.Within)).isSome then
          sampler := true
        for forbidden in #[``Bounds, ``GeneralCaller.Budget, ``Program, ``SourceCertificate, ``Fintype, ``Finite,
            ``Expression.compile, ``Expression.compileBound] do
          if (type.find? (fun e => e.isConstOf forbidden)).isSome then
            throwError "{name}: derive full caller costs and invariants from measured arbitrary executions"
        let userName := (← getFVarLocalDecl param).userName
        if #[`callerInv, `hcallerStep, `hcallerWidth, `hhandler, `hbudget].contains userName then
          throwError "{name}: discharge caller invariants and finished handler budgets internally"
      unless measured && actual do
        throwError "{name}: require measured resources and the actual executed native caller"
      if name == ``NativeHandler.caller_bound_of_resources then
        unless sampler do
          throwError "derive private and challenge sampling costs from the original profile"
  for name in #[``NativeHandler.callerTime_polynomial, ``NativeHandler.callerResourcesTime_polynomial] do
    forallTelescope (← getConstInfo name).type fun params _ => do
      for param in params do
        let userName := (← getFVarLocalDecl param).userName
        if #[`arityCap, `counter, `counterCap, `domainSize].contains userName then
          throwError "{name}: do not require polynomial numeric arities/counters or a finite message universe"

end SignaturesTest.SchnorrROMCaller
