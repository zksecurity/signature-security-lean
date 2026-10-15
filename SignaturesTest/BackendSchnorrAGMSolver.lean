import Signatures.Runtime.BackendSchnorrAGMSolverCorrectness
import Signatures.Runtime.BackendSchnorrAGMSolverDescription
import Signatures.Runtime.BackendSchnorrAGMSolverSetup
import Signatures.Runtime.BackendSchnorrAGMSecurity
import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation
open Signatures.Runtime Signatures.Runtime.BackendProgram Signatures.Runtime.SchnorrAGM.Native

namespace SignaturesTest.BackendSchnorrAGMSolver

private instance : Fact (Nat.Prime 7) := ⟨by decide⟩
private abbrev F := ZMod 7

section Native

variable {C : StepClass} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass C} [Q.HasCategory] [Q.HasProd] [Q.HasSum] [Q.IsDistributive]
  {iface : BackendProgram.Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F F F Nat Nat))
  (bd : Boundary C (Interface.sourceSpec F F Nat).toPFunctor (Solver.SourceInput F) (Interface.SourceForgery F F Nat))
  (boundary : Solver.DataPorts (Q := Q) rep bd)
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F F F Nat Nat cost).execute instr))
  (sampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))

-- The public input and chronological initial basis have the same order, and
-- no cache, signed-message history or failure flag is initialized implicitly.
example : (Solver.setup (iface := iface) rep bd boundary data cost primitive).denote (1, 3, ()) =
    pure (⟨(), fun _ => [1, 3]⟩, (1, 3), [], [(1, 0), (0, 1)], [], false, false) := by
  rw [Solver.setup_denote]
  rfl

-- A missing return takes the zero fallback for arbitrary accumulated state.
example (saved : (F × F) × EncodedState F F Nat) :
    (Solver.terminal rep bd boundary data cost primitive (Extraction.code rep data cost primitive sampler)).denote
      (none, saved) = pure (0 : F) := by
  rw [Solver.terminal_denote]

-- The actual caller-output conversion and terminal projection preserve the
-- first cached explanation. The discarded acceptance Boolean is not a filter
-- on the DLog solver's scalar, even when the malformed flag is already set.
example :
    (Solver.terminal rep bd boundary data cost primitive (Extraction.code rep data cost primitive sampler)).denote
      (some (Interface.decodeForgery ((7, 6), [1], [[1, 3]])), (1, 3),
        [((7, 1), (2, true, 1, 3)), ((7, 1), (4, false, 2, 3))], [(1, 0), (0, 1)], [], true, false) =
      pure (1 : F) := by
  rw [Solver.terminal_denote]
  dsimp only
  rw [Interface.encode_decodeForgery, Extraction.denote]
  dsimp only
  rw [Extraction.decoded_denote, EntryRead.denote, cacheAccess_denote]
  simp only [Hash.prepareValue, Read.packValue, Read.setupValue, cacheMap,
    ↓reduceIte, map_pure, EntryRead.returnValue, Extraction.solutionValue]
  norm_num
  decide

end Native

open Lean Meta in
run_meta do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``Solver.DataPorts.mk, ``Solver.setup_denote, ``Solver.finishSome_denote,
      ``Solver.cutoff_denote, ``Solver.terminal_denote, ``Solver.terminal_none_run,
      ``Solver.program_denote, ``Solver.program_source_of_resources,
      ``Solver.setup_description, ``Solver.finishSome_description, ``Solver.cutoff_description,
      ``Solver.terminal_description, ``Solver.program_description,
      ``Solver.initial_reserved, ``Solver.initial_cost, ``Solver.cutoff_cost, ``Solver.cutoff_bound,
      ``Solver.projection_bound, ``Solver.setup_bound,
      ``Solver.adaptOutput_bound_with_widths, ``Extraction.input_of_state,
      ``Solver.PortCaps.mk, ``Solver.finishSome_bound_of_extractor, ``Solver.cutoff_bound_of_store,
      ``Solver.terminal_bound_of_extractor, ``Solver.terminal_bound, ``Solver.program_bound,
      ``Solver.program_description_uniform, ``Solver.program_within, ``Solver.challenge_size,
      ``Solver.security_of_resources] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"
    forallTelescope (← getConstInfo name).type fun params _ => do
      for param in params do
        let type ← inferType param
        if type.isAppOf ``Finite || type.isAppOf ``Fintype then
          let domain := type.getAppArgs[0]!
          unless name == ``Solver.security_of_resources && domain.isFVar &&
              (← domain.fvarId!.getUserName) == `F do
            throwError "{name}: unexpected finite-domain premise"
        for forbidden in #[``Solver.program, ``Solver.setup, ``Solver.terminal, ``Solver.finishSome,
            ``Extraction.code, ``Handler.caller,
            `Signatures.Runtime.AGM.SourceCertificate, `Signatures.Runtime.Schnorr.SourceCertificate,
            `Signatures.Runtime.GeneralCaller.Budget] do
          if (type.find? (fun e => e.isConstOf forbidden)).isSome then
            throwError "{name}: assumed complete-program budget or restricted attacker"

end SignaturesTest.BackendSchnorrAGMSolver
