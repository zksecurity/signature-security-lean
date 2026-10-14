import Signatures.Runtime.BackendLazyAGMCallerResources
import Signatures.Runtime.BackendLazyAGMCallerOutput
import Signatures.Runtime.BackendLazyAGMHandlerDescription
import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

open OracleComp OracleSpec PFunctor
open Signatures.Runtime Signatures.Runtime.BackendProgram Signatures.Runtime.Coron
open Signatures.Runtime.LazyAGM Signatures.Runtime.LazyAGM.NativeHandler
open PFunctor.DynSystem.DynComputation

namespace SignaturesTest.BackendLazyAGMHandler

set_option backward.isDefEq.respectTransparency false
attribute [local implicit_reducible] PFunctor.Idx

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

section Native

variable {C : StepClass} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass C} [Q.HasCategory] [Q.HasProd] [Q.HasSum] [Q.IsDistributive]
  {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase (ZMod 5) (ZMod 5) (ZMod 5) Nat Nat))
  (bd : Boundary C (generalSpec Nat (ZMod 5) 4).toPFunctor (ZMod 5) (Model.LazyAGM.Output (ZMod 5) Nat))
  (ports : NativePorts (Q := Q) rep bd) (sampler : BoundedSampler rep bd ports (iface := iface))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic (ZMod 5) (ZMod 5) (ZMod 5) Nat Nat cost).execute instr))
  (sampling : MachineCompiler.SamplingImplementation Q iface rep)

-- A hash hit reuses the private scalar and still records the chronological
-- reply, with the original request restored in the dependent response tag.
example : (goodCode rep bd ports sampler data cost primitive sampling).denote
    (.inl (.inr 7), (3, 4), [(7, 2)], ([], [])) =
      pure (tagGroup false (7, (1 : ZMod 5)), (3, 4), [(7, 2)], ([(7, 1)], [])) := by
  rw [SignatureHandler.code_denote]
  simp only [SignatureHandler.source, StateT.run]
  rw [backendGoodReply_denote, BLS.LazyAGM.Reduction.privateListOracle_lookup]
  norm_num [List.lookup_cons, record, tagGroup, smul_eq_mul]
  change (2 : ZMod 5) * 3 = 1
  decide

-- Signing before hashing and repeated cache hits retain two distinct reply
-- tokens without adding another cache entry. Both calls execute native dispatch.
example : (do
    let p ← (badCode rep bd ports sampler data cost primitive sampling).denote
      (.inr 7, (4, 3, 1), [(7, (2, 3))], ([], []))
    (badCode rep bd ports sampler data cost primitive sampling).denote (.inl (.inr 7), p.2)) =
      pure (tagGroup false (7, (1 : ZMod 5)), (4, 3, 1), [(7, (2, 3))], ([(7, 1)], [(7, 4)])) := by
  rw [SignatureHandler.code_denote]
  simp only [SignatureHandler.source, StateT.run]
  rw [backendBadReply_denote, BLS.LazyAGM.Reduction.privateListOracle_lookup]
  norm_num [List.lookup_cons, record, tagGroup, smul_eq_mul]
  rw [SignatureHandler.code_denote]
  simp only [SignatureHandler.source, StateT.run]
  rw [backendBadReply_denote, BLS.LazyAGM.Reduction.privateListOracle_lookup]
  norm_num [List.lookup_cons, record, tagGroup, smul_eq_mul]
  change (11 : ZMod 5) = 1 ∧ (44 : ZMod 5) = 4
  decide

-- The bounded randomness request passes through one dynamic sampler and
-- leaves both the cache and the existing transcript unchanged.
example (n : Fin 5)
    (saved : (storeTy scalar goodConfigTy).Value (cryptoBase (ZMod 5) (ZMod 5) (ZMod 5) Nat Nat)) :
    (goodCode rep bd ports sampler data cost primitive sampling).denote (.inl (.inl n), saved) =
      (fun r => (tagRandom (M := Nat) (G₁ := ZMod 5) ⟨n, r⟩, saved)) <$>
        (liftM (unifSpec.query n.val) : ProbComp (Fin (n.val + 1))) := by
  rw [SignatureHandler.code_denote]
  simp only [SignatureHandler.source, StateT.run]
  rfl

variable [C.HasOption] [Q.HasOption] [OptionCode (Q := Q)]
  (R : GeneralCaller.Caller (Q := Q) (bd := bd))

-- A zero-query attacker still returns its complete algebraic output when
-- fuel is zero; the native loop must not mistake terminal readout for cutoff.
example (input : ZMod 5) (out : Model.LazyAGM.Output (ZMod 5) Nat)
    (hv : R.machine.view (R.machine.init input) = .inl out)
    (saved : (storeTy scalar goodConfigTy).Value (cryptoBase (ZMod 5) (ZMod 5) (ZMod 5) Nat Nat)) :
    (goodCaller rep bd ports sampler data cost primitive sampling R 0).denote (input, saved) =
      pure (some out, saved) := by
  rw [SignatureHandler.caller_denote]
  simp [runWithInput, runWith, unroll, hv]

-- The zero-fuel query case remains an explicit cutoff and does not alter the
-- cache or transcript. The resource-to-termination theorem rules this case out
-- when fuel covers the attacker's measured query bound.
example (input : ZMod 5) (i : GeneralRequest Nat 4)
    (next : (generalSpec Nat (ZMod 5) 4).Range i → R.machine.State)
    (hv : R.machine.view (R.machine.init input) = .inr ⟨i, next⟩)
    (saved : (storeTy (.pair scalar scalar) badConfigTy).Value (cryptoBase (ZMod 5) (ZMod 5) (ZMod 5) Nat Nat)) :
    (badCaller rep bd ports sampler data cost primitive sampling R 0).denote (input, saved) =
      pure (none, saved) := by
  rw [SignatureHandler.caller_denote]
  simp [runWithInput, runWith, unroll, hv]

end Native

-- Check the complete dispatcher certificates, adaptive caller source laws,
-- and their supporting resource lemmas without a finite message-domain premise.
open Lean Meta in
run_meta do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``SignatureHandler.group_denote, ``SignatureHandler.random_denote,
      ``SignatureHandler.code_denote, ``SignatureHandler.code_executed_run,
      ``SignatureHandler.executed_erase, ``SignatureHandler.caller_denote, ``SignatureHandler.caller_erase,
      ``SignatureHandler.request_size, ``SignatureHandler.random_bound, ``SignatureHandler.group_bound,
      ``SignatureHandler.code_bound, ``SignatureHandler.group_description,
      ``SignatureHandler.random_description, ``SignatureHandler.code_description,
      ``goodSource_refines, ``badSource_refines, ``goodCaller_source, ``badCaller_source,
      ``reserved_weaken, ``goodReserved_size, ``badReserved_size,
      ``goodReply_reserved, ``badReply_reserved, ``goodCode_bound, ``badCode_bound,
      ``goodCode_description, ``badCode_description,
      ``SignatureHandler.executed_mem_code, ``SignatureHandler.caller_bound,
      ``SignatureHandler.RequestRecovery.canonical,
      ``SignatureHandler.reachable_request, ``SignatureHandler.reachable_output,
      ``SignatureHandler.resource_step, ``SignatureHandler.caller_bound_of_resources,
      ``SignatureHandler.caller_reference_denote, ``SignatureHandler.caller_output_invariant,
      ``SignatureHandler.caller_output_size_of_resources,
      ``SignatureHandler.caller_source_of_resources, ``SignatureHandler.caller_no_cutoff_of_resources,
      ``caller_output_bounds_of_resources,
      ``goodCaller_bound, ``badCaller_bound,
      ``goodCaller_bound_of_resources, ``badCaller_bound_of_resources,
      ``SignatureHandler.caller_description, ``goodCaller_description, ``badCaller_description] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"
    forallTelescope (← getConstInfo name).type fun params _ => do
      for param in params do
        let type ← inferType param
        if type.isAppOf ``Finite || type.isAppOf ``Fintype then
          throwError "{name}: finite-domain premise added to lazy dispatch"

-- Resource endpoints must derive caller invariants/budgets and concrete native
-- dispatcher costs. A whole-code Bounds premise or arithmetic-source certificate
-- would reintroduce the gap these endpoints are intended to close.
open Lean Meta in
run_meta do
  for name in #[``goodCaller_bound_of_resources, ``badCaller_bound_of_resources] do
    forallTelescope (← getConstInfo name).type fun params _ => do
      for param in params do
        let type ← inferType param
        for forbidden in #[``Bounds, ``GeneralCaller.Budget,
            `Signatures.Runtime.AGM.SourceCertificate,
            `Signatures.Runtime.Coron.SourceCertificate,
            `Signatures.Runtime.Schnorr.SourceCertificate] do
          if type.find? (fun e => e.isConstOf forbidden) |>.isSome then
            throwError "{name}: forbidden whole-component budget or arithmetic attacker restriction: {forbidden}"

end SignaturesTest.BackendLazyAGMHandler
