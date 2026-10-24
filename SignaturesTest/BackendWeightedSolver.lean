import Proofs.Runtime.BackendWeightedSolverCorrectness
import Proofs.Runtime.BackendWeightedSolverWithin
import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

open OracleComp OracleSpec PFunctor
open Signatures.Runtime Signatures.Runtime.BackendProgram
open Signatures.Runtime.WeightedAGM Signatures.Runtime.WeightedAGM.NativeSolver
open Signatures.Runtime.WeightedAGM.NativeHandler
open PFunctor.DynSystem.DynComputation

namespace SignaturesTest.BackendWeightedSolver

attribute [local implicit_reducible] PFunctor.Idx

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

variable {C : StepClass} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass C}
  [Q.HasCategory] [Q.HasProd] [Q.HasSum] [Q.HasOption] [Q.IsDistributive] [OptionCode (Q := Q)]
  {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase (ZMod 5) (ZMod 5) (ZMod 5) Nat Bool))
  (bd : Boundary C (generalSpec (Nat × Fin 2) (ZMod 5 × Nat) (ZMod 5) 4).toPFunctor (ZMod 5)
    ((AGM.outputTy (Index.oops 1).messageTy).Value (cryptoBase (ZMod 5) (ZMod 5) (ZMod 5) Nat Bool)))
  (ports : NativePorts (Q := Q) rep (Index.oops 1).ty (Index.oops 1).messageTy bd) (sampler : BoundedSampler rep (Index.oops 1).ty (Index.oops 1).messageTy bd ports (iface := iface))
  (boundary : DataPorts (Q := Q) rep (.oops 1) bd)
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic (ZMod 5) (ZMod 5) (ZMod 5) Nat Bool cost).execute instr))
  (sampling : MachineCompiler.SamplingImplementation Q iface rep)
  (R : GeneralCaller.Caller (Q := Q) (bd := bd))

-- Use distinct key/message types and arbitrary natural topics.
-- A challenge contains two G1 points and two G2 points. Check the complete
-- good program at insufficient fuel, rather than only its terminal helper.
example (g X g₂ pk : ZMod 5) (next : ZMod 5 → R.machine.State)
    (hv : R.machine.view (R.machine.init pk) = .inr ⟨.inr ((3 : ZMod 5), 7), next⟩) :
    (goodProgram rep (.oops 1) bd ports sampler boundary data cost primitive sampling R 0).denote (g, X, g₂, pk, ()) =
      pure (0 : ZMod 5) := by
  rw [goodProgram_denote, NativeHandler.caller_denote]
  simp [runWithInput, runWith, unroll, hv]
  rw [terminal_denote]

-- The bad program chooses its own public key and still samples the secret on
-- the cutoff path. Its computation must retain that randomness operation.
example (g X g₂ pk : ZMod 5) (next : ZMod 5 → ZMod 5 → R.machine.State)
    (hv : ∀ key, R.machine.view (R.machine.init key) = .inr ⟨.inr ((3 : ZMod 5), 7), next key⟩) :
    (badProgram rep (.oops 1) bd ports sampler boundary data cost primitive sampling R 0).denote (g, X, g₂, pk, ()) =
      (fun _ : ZMod 5 => (0 : ZMod 5)) <$> ($ᵗ (ZMod 5) : ProbComp (ZMod 5)) := by
  rw [badProgram_denote, ← bind_pure_comp]
  apply bind_congr
  intro kappa
  rw [NativeHandler.caller_denote]
  simp [runWithInput, runWith, unroll, hv]
  rw [terminal_denote]

open Lean Meta in
run_meta do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``setupGood_denote, ``setupBad_denote, ``finishSome_denote,
      ``cutoff_denote, ``terminal_denote, ``goodProgram_denote, ``badProgram_denote,
      ``goodProgram_source, ``badProgram_source,
      ``goodProgram_source_of_resources, ``badProgram_source_of_resources,
      ``atomic_bound_of_width, ``seq_bound_of_width, ``first_bound_of_width,
      ``initial_reserved, ``initialGood_cost, ``initialBad_cost,
      ``extractionArgsExpr_cost, ``extractionArgsCode_cost,
      ``setupGood_bound, ``setupBad_bound,
      ``finishSome_bound_of_extractor, ``cutoff_bound, ``terminal_bound_of_extractor,
      ``goodTerminal_bound, ``badTerminal_bound,
      ``goodProgram_bound, ``badProgram_bound,
      ``termsDescription_le, ``setupGood_description, ``setupBad_description, ``extractionArgsCode_description,
      ``finishSome_description, ``cutoff_description, ``terminal_description,
      ``goodProgram_description, ``badProgram_description,
      ``goodProgram_within, ``badProgram_within] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"
    forallTelescope (← getConstInfo name).type fun params _ => do
      for param in params do
        let type ← inferType param
        if type.isAppOf ``Finite || type.isAppOf ``Fintype then
          throwError "{name}: finite-domain premise added to the native solver"

-- Concrete budgets must be derived from primitive contracts and the attacker's
-- resources, including after setup and extraction have been composed.
open Lean Meta in
run_meta do
  for name in #[``setupGood_bound, ``setupBad_bound, ``goodTerminal_bound, ``badTerminal_bound,
      ``goodProgram_bound, ``badProgram_bound, ``goodProgram_within, ``badProgram_within] do
    forallTelescope (← getConstInfo name).type fun params _ => do
      for param in params do
        let type ← inferType param
        for forbidden in #[``Bounds, ``GeneralCaller.Budget,
            `Signatures.Runtime.AGM.SourceCertificate,
            `Signatures.Runtime.Coron.SourceCertificate,
            `Signatures.Runtime.Schnorr.SourceCertificate] do
          if type.find? (fun e => e.isConstOf forbidden) |>.isSome then
            throwError "{name}: assumed component budget or restricted attacker: {forbidden}"

-- Whole-solver endpoints derive their cache, transcript, and caller invariants.
-- They must retain the measured attacker bound and source-realization contract.
open Lean Meta in
run_meta do
  for name in #[``goodProgram_bound, ``badProgram_bound, ``goodProgram_within, ``badProgram_within] do
    forallTelescope (← getConstInfo name).type fun params _ => do
      let mut measured := false
      let mut realized := false
      for param in params do
        let binder ← param.fvarId!.getUserName
        let type ← inferType param
        if binder == `hrun then
          measured := (type.find? (fun e => e.isConstOf
            ``QuantitativeRealization.RunsWithin)).isSome
        if binder == `hprogram then
          realized := (type.find? (fun e => e.isConstOf
            ``PFunctor.DynSystem.DynComputation.Implements)).isSome
        for forbidden in #[``Model.LazyAGM.WeightedReduction.TranscriptCached,
            ``NativeHandler.ReservedState, ``ExtractionReady, ``ResultReady,
            ``GeneralCaller.Reachable, ``Within] do
          if (type.find? (fun e => e.isConstOf forbidden)).isSome then
            throwError "{name}: supplied full solver certificate or internal invariant: {forbidden}"
      unless measured && realized do
        throwError "{name}: missing measured execution or source realization"

end SignaturesTest.BackendWeightedSolver
