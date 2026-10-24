import Proofs.Runtime.BackendLazyAGMReplyDescription
import Proofs.Runtime.BackendLazyAGMStateSize
import Proofs.Runtime.BackendLazyAGMReplyBudget
import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

open OracleComp OracleSpec PFunctor Signatures.Runtime Signatures.Runtime.BackendProgram
open Signatures.Runtime.LazyAGM Model.LazyAGM BLS.LazyAGM.Reduction

namespace SignaturesTest.BackendLazyAGMReply

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private def repeated : OracleComp (advSpec Nat Nat (ZMod 5)) (ZMod 5 × ZMod 5 × ZMod 5) := do
  let s₁ : ZMod 5 ← liftM ((advSpec Nat Nat (ZMod 5)).query (.inr 7))
  let h : ZMod 5 ← liftM ((advSpec Nat Nat (ZMod 5)).query (.inl (.inr 7)))
  let s₂ : ZMod 5 ← liftM ((advSpec Nat Nat (ZMod 5)).query (.inr 7))
  pure (s₁, h, s₂)

private def adaptive : OracleComp (advSpec Nat Nat (ZMod 5)) (Output (ZMod 5) Nat) := do
  let bit : Fin 2 ← liftM ((advSpec Nat Nat (ZMod 5)).query (.inl (.inl 1)))
  let s : ZMod 5 ← liftM ((advSpec Nat Nat (ZMod 5)).query (.inr (7 + bit.val)))
  let _ : ZMod 5 ← liftM ((advSpec Nat Nat (ZMod 5)).query (.inl (.inr s.val)))
  let _ : ZMod 5 ← liftM ((advSpec Nat Nat (ZMod 5)).query (.inr (7 + bit.val)))
  pure ⟨s.val + 100, 1, [2, 3], [4]⟩

section Execution

variable {C : StepClass} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass C} [Q.HasCategory] [Q.HasProd] [Q.HasSum]
  {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase (ZMod 5) (ZMod 5) (ZMod 5) Nat Nat))
  (data : DataCode Q rep.data) (sampling : MachineCompiler.SamplingImplementation Q iface rep)
  (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic (ZMod 5) (ZMod 5) (ZMod 5) Nat Nat cost).execute instr))

-- Signing before hashing reuses the same private scalar. Every explicit reply
-- still gets an occurrence, including the repeated signature on a cache hit.
example : (simulateQ (backendGoodOracle rep data cost primitive sampling 1 3) repeated).run
    ([(7, 2)], ([(8, 4)], [])) =
      pure ((1, 2, 1), [(7, 2)], ([(7, 2), (8, 4)], [(7, 1), (7, 1)])) := by
  rw [backendGoodOracle_eq]
  simp only [repeated, simulateQ_bind, simulateQ_spec_query, simulateQ_pure,
    StateT.run_bind, StateT.run_pure]
  erw [listOracle_sign, privateListOracle_lookup]
  simp only [List.lookup_cons_self, map_pure, pure_bind]
  erw [listOracle_hash, privateListOracle_lookup]
  simp only [List.lookup_cons_self, map_pure, pure_bind]
  erw [listOracle_sign, privateListOracle_lookup]
  simp only [List.lookup_cons_self, map_pure, pure_bind]
  norm_num [record]
  decide

-- The bad branch uses the same two masks for both reply modes; signing scales
-- the masked group point by the privately chosen signing key.
example : (backendBadReply rep data cost primitive sampling true).denote
    (7, ((2 : ZMod 5), 1, 3), [(7, (2, 1))], ([], [])) =
      pure ((4 : ZMod 5), ((2 : ZMod 5), 1, 3), [(7, (2, 1))], ([], [(7, 4)])) := by
  rw [backendBadReply_denote, privateListOracle_lookup]
  simp only [List.lookup_cons_self, map_pure, ite_true]
  norm_num [record]
  decide

-- Correspondence covers private random choices and reply-dependent requests,
-- retaining the output (including coefficient lists), final cache, and transcript.
example : observe <$> (simulateQ (backendGoodOracle rep data cost primitive sampling 1 3) adaptive).run
    ([], ([], [])) =
      (simulateQ privateListOracle
        ((simulateQ (privateOracle (fun rho : ZMod 5 => rho • (1 : ZMod 5))
          (fun rho => rho • (3 : ZMod 5))) adaptive).run ([], []))).run [] := by
  exact backendGoodSimulation rep data cost primitive sampling 1 3 adaptive [] ([], [])

example : observe <$> (simulateQ (backendBadOracle rep data cost primitive sampling 1 3 2) adaptive).run
    ([], ([], [])) =
      (simulateQ privateListOracle
        ((simulateQ (privateOracle (fun masks : ZMod 5 × ZMod 5 => masks.1 • (3 : ZMod 5) + masks.2 • (1 : ZMod 5))
          (fun masks => (2 : ZMod 5) • (masks.1 • (3 : ZMod 5) + masks.2 • (1 : ZMod 5)))) adaptive).run
            ([], []))).run [] := by
  exact backendBadSimulation rep data cost primitive sampling 1 3 2 adaptive [] ([], [])

example (out : Output (ZMod 5) Nat × State Nat (ZMod 5) (ZMod 5))
    (hout : out ∈ support ((simulateQ (backendGoodOracle rep data cost primitive sampling 1 3) adaptive).run
      ([], ([], [])))) : out.2.1.length ≤ 4 ∧ out.2.2.1.length + out.2.2.2.length ≤ 4 := by
  rw [backendGoodOracle_eq] at hout
  have hq : IsTotalQueryBound adaptive 4 := by simp [adaptive, IsTotalQueryBound]
  simpa using listSimulation_growth _ _ adaptive ([], ([], [])) 4 hq out hout

end Execution

example : chronological ([(7, (2 : ZMod 5)), (8, 4)], [(7, 1), (9, 3)]) =
    ([(8, (4 : ZMod 5)), (7, 2)], [(9, 3), (7, 1)]) := rfl

-- Transcript storage counts repeated delivered replies, not only distinct keys.
example : State.Messages (fun m : Nat => m = 7)
    ([(7, (0 : ZMod 5))], ([(7, (0 : ZMod 5)), (7, 0)], [(7, 0)])) := by
  simp [State.Messages]

open Lean Meta Elab Command

run_cmd liftTermElabM do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``chronological_record, ``cacheArgs_denote, ``replyResult_denote,
      ``goodResponse_denote, ``badResponse_denote,
      ``Expression.variableDescription_weakenTail, ``Expression.descriptionBound_weakenTail,
      ``cacheArgs_description, ``replyResult_description, ``goodResponse_description, ``badResponse_description,
      ``replyBody_denote, ``backendReply_denote, ``backendGoodReply_denote, ``backendBadReply_denote,
      ``listSimulation, ``listRun, ``listReply_growth, ``listReply_messages,
      ``listOracle_growth, ``listSimulation_growth, ``backendReply_state,
      ``backendGoodOracle_eq, ``backendBadOracle_eq, ``backendGoodSimulation, ``backendBadSimulation,
      ``replyBody_description, ``backendReply_description, ``backendGoodReply_description, ``backendBadReply_description,
      ``store_encoded_size, ``goodStore_encoded_size, ``badStore_encoded_size,
      ``goodCacheArgs_cost, ``badCacheArgs_cost, ``goodReplyResult_cost, ``badReplyResult_cost,
      ``replyFrame_size, ``cacheArgs_size, ``replyResult_size,
      ``backendReply_bound, ``backendGoodReply_bound, ``backendBadReply_bound] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"
  for name in #[``backendGoodReply, ``backendBadReply, ``listSimulation, ``listSimulation_growth,
      ``backendGoodSimulation, ``backendBadSimulation,
      ``backendGoodReply_description, ``backendBadReply_description,
      ``goodStore_encoded_size, ``badStore_encoded_size,
      ``backendGoodReply_bound, ``backendBadReply_bound] do
    forallTelescope (← getConstInfo name).type fun params _ => do
      for param in params do
        let type ← inferType param
        if type.isAppOf ``Finite || type.isAppOf ``Fintype then
          if let .fvar id := type.getAppArgs[0]! then
            if (← id.getUserName) == `M then
              throwError "{name}: finite-message premise added to a lazy reply or simulation"

end SignaturesTest.BackendLazyAGMReply
