import Signatures.Runtime.BackendSchnorrAGMExtractionDescription
import Signatures.Runtime.BackendSchnorrAGMExtractionBudget
import Signatures.Runtime.BackendSchnorrAGMExtractionResources
import Signatures.Runtime.BackendSchnorrAGMSolverOutput
import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

open OracleComp OracleSpec PFunctor Schnorr.AGM
open PFunctor.DynSystem.DynComputation
open Signatures.Runtime Signatures.Runtime.BackendProgram Signatures.Runtime.SchnorrAGM.Native

namespace SignaturesTest.BackendSchnorrAGMExtraction

private instance : Fact (Nat.Prime 7) := ⟨by decide⟩
private abbrev F := ZMod 7

section Native

variable {C : StepClass} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass C} [Q.HasCategory] [Q.HasProd] [Q.HasSum] [Q.IsDistributive]
  {iface : BackendProgram.Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F F F Nat Nat))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F F F Nat Nat cost).execute instr))
  (sampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))

-- The first cached explanation controls extraction. The later coefficient
-- vector and a shadowed entry do not replace it, and a cache hit never samples.
example : (Extraction.code rep data cost primitive sampler).denote
    (((7, 6), [1], [[5, 6, 2]]), [((7, 1), (2, true, 1, 3)), ((7, 1), (5, true, 3, 4))],
      [(1, 0), (0, 1)], [8], true, false) =
    pure (1, [((7, 1), (2, true, 1, 3)), ((7, 1), (5, true, 3, 4))],
      [(1, 0), (0, 1)], [8], true, false) := by
  rw [Extraction.denote]
  dsimp only
  rw [Extraction.decoded_denote, EntryRead.denote, cacheAccess_denote]
  simp only [Hash.prepareValue, Read.packValue, Read.setupValue, cacheMap,
    ↓reduceIte, map_pure, EntryRead.returnValue, Extraction.solutionValue]
  norm_num
  decide

-- A signing entry with no explanation must return zero, even when its unused
-- affine slots are nonzero and a shadowed entry has an explanation.
example : (Extraction.code rep data cost primitive sampler).denote
    (((7, 6), [1], [[1, 3]]), [((7, 1), (2, false, 4, 5)), ((7, 1), (2, true, 1, 3))],
      [(1, 0), (0, 1)], [7], false, true) =
    pure (0, [((7, 1), (2, false, 4, 5)), ((7, 1), (2, true, 1, 3))],
      [(1, 0), (0, 1)], [7], false, true) := by
  rw [Extraction.denote]
  dsimp only
  rw [Extraction.decoded_denote, EntryRead.denote, cacheAccess_denote]
  simp only [Hash.prepareValue, Read.packValue, Read.setupValue, cacheMap,
    ↓reduceIte, map_pure, EntryRead.returnValue, Extraction.solutionValue]
  rfl

-- Rejected final shapes preserve the malformed flag as well as every cache
-- and history entry. They must not use the hash handler's rejection update.
example (saved : EncodedState F F Nat) : (Extraction.code rep data cost primitive sampler).denote
    (((7, 6), [1, 1], [[], [1, 3]]), saved) = pure (0, saved) := by
  rw [Extraction.denote]

-- A fresh final target is sampled once, cached with the flattened explanation,
-- and extracted using that same challenge. Nat messages are not a finite domain.
example (hs : sampler.denote () = pure (2 : F)) :
    (Extraction.code rep data cost primitive sampler).denote
      (((7, 6), [1], [[1, 3]]), [], [(1, 0), (0, 1)], [8], false, false) =
    pure (1, [((7, 1), (2, true, 1, 3))], [(1, 0), (0, 1)], [8], false, false) := by
  rw [Extraction.denote]
  dsimp only
  rw [Extraction.decoded_denote, EntryRead.denote, cacheAccess_denote]
  simp only [Hash.prepareValue, Read.packValue, Read.setupValue, cacheMap, hs, map_pure]
  norm_num [Flatten.value, Extraction.solutionValue, EntryRead.returnValue, freshValue,
    Flatten.total]
  decide

-- The exceptional denominator is handled exactly as in the source: division
-- yields zero and the freshly read entry sets the bad-event flag.
example (hs : sampler.denote () = pure (4 : F)) :
    (Extraction.code rep data cost primitive sampler).denote
      (((7, 6), [1], [[1, 3]]), [], [(1, 0), (0, 1)], [], false, false) =
    pure (0, [((7, 1), (4, true, 1, 3))], [(1, 0), (0, 1)], [], false, true) := by
  rw [Extraction.denote]
  dsimp only
  rw [Extraction.decoded_denote, EntryRead.denote, cacheAccess_denote]
  simp only [Hash.prepareValue, Read.packValue, Read.setupValue, cacheMap, hs, map_pure]
  norm_num [Flatten.value, Extraction.solutionValue, EntryRead.returnValue, freshValue,
    Flatten.total]
  decide

-- The executable output boundary retains surplus group/row data and the full
-- private state. The public generator/key configuration can be discarded here.
example
    (bd : Boundary C (Interface.sourceSpec F F Nat).toPFunctor Unit (Interface.SourceForgery F F Nat))
    (convert : Q.Realizer bd.out (rep.ty Interface.forgeryTy) Interface.encodeForgery)
    (saved : EncodedState F F Nat) :
    (Solver.adaptOutput (iface := iface) rep bd convert).denote
      (Interface.decodeForgery ((7, 6), [1, 2], [[1, 3], [6, 5, 4]]), (1, 2), saved) =
      pure (((7, 6), [1, 2], [[1, 3], [6, 5, 4]]), saved) := by
  rw [Solver.adaptOutput_denote]
  rfl

end Native

open Lean Meta in
run_meta do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``SchnorrAGM.readEntry_challenge, ``SchnorrAGM.readEntry_cached,
      ``SchnorrAGM.finishScalar_eq, ``SchnorrAGM.dlogReduction_finishScalar,
      ``EntryRead.denote, ``EntryRead.source, ``EntryRead.hit_run, ``EntryRead.histories_run,
      ``EntryRead.return_property, ``EntryRead.output_size, ``EntryRead.finish_cost,
      ``EntryRead.bound, ``EntryRead.description,
      ``Extraction.finishExpression_value, ``Extraction.solution_encode,
      ``Extraction.decoded_denote, ``Extraction.denote, ``Extraction.malformed_run, ``Extraction.source,
      ``Extraction.source_finish, ``Extraction.localCode_description,
      ``Extraction.decoded_description, ``Extraction.description,
      ``Extraction.start_cost, ``Extraction.reject_cost, ``Extraction.finish_cost,
      ``Extraction.prepared_bound, ``Extraction.decoded_bound,
      ``Extraction.width_le_frame, ``Extraction.hash_frame_le, ``Extraction.starting_size,
      ``Extraction.input_size, ``Extraction.decoded_size, ``Extraction.routed_size,
      ``Extraction.reject_property, ``Extraction.start_bound, ``Extraction.route_bound,
      ``Extraction.reject_bound, ``Extraction.bound,
      ``Extraction.input_of_forgery_size, ``Extraction.input_of_store,
      ``Solver.adaptOutput_denote, ``Solver.outputArgs_description, ``Solver.adaptOutput_description,
      ``Solver.outputArgs_cost, ``Solver.adaptOutput_bound] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"
    forallTelescope (← getConstInfo name).type fun params _ => do
      for param in params do
        let type ← inferType param
        if type.isAppOf ``Finite || type.isAppOf ``Fintype then
          throwError "{name}: unexpected finite-domain premise"
        for forbidden in #[``EntryRead.code, ``Extraction.code, ``Extraction.decoded, ``Extraction.prepared,
            ``Read.code, ``Hash.code, ``HashDispatch.code, ``cacheAccess, ``Solver.adaptOutput,
            `Signatures.Runtime.AGM.SourceCertificate, `Signatures.Runtime.Schnorr.SourceCertificate,
            `Signatures.Runtime.GeneralCaller.Budget] do
          if (type.find? (fun e => e.isConstOf forbidden)).isSome then
            -- The histories theorem assumes a supported run, not its budget.
            unless forbidden == ``EntryRead.code && type.isAppOf ``Membership.mem do
              throwError "{name}: assumed completed component budget or restricted attacker"

end SignaturesTest.BackendSchnorrAGMExtraction
