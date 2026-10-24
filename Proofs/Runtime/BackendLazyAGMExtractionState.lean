import Proofs.Runtime.BackendLazyAGMEvaluateState
import Proofs.Runtime.BackendLazyAGMExtractionGrowth

/-! Private-cache key invariants across complete evaluator calls. These
semantic invariants retain the original message-size predicate while later
runtime composition retains larger aggregate argument and cache frames. -/

open OracleComp OracleSpec PFunctor Model.LazyAGM BLS.LazyAGM.Reduction

namespace Signatures.Runtime.LazyAGM

open BackendProgram

theorem privateTerms_messages {F M R : Type} [DecidableEq M] [SampleableType R]
    [AddCommMonoid R] [SMul F R]
    (p : M → Prop) (terms : List (M × F)) (cache : List (M × R))
    (ht : ∀ term ∈ terms, p term.1) (hc : ∀ entry ∈ cache, p entry.1)
    (out : R × List (M × R))
    (hout : out ∈ support ((simulateQ (privateListOracle (M := M) (R := R)) (evalTerms terms)).run cache)) :
    ∀ entry ∈ out.2, p entry.1 := by
  induction terms generalizing cache out with
  | nil =>
      simp only [evalTerms, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hout
      subst out
      exact hc
  | cons term terms ih =>
      simp only [evalTerms, simulateQ_bind, simulateQ_spec_query, simulateQ_pure,
        StateT.run_bind, StateT.run_pure, mem_support_bind_iff,
        support_pure, Set.mem_singleton_iff] at hout
      obtain ⟨mid, hmid, rest, hrest, rfl⟩ := hout
      exact ih mid.2 (fun t h => ht t (List.mem_cons_of_mem _ h))
        (privateRead_messages p term.1 cache (ht term (by simp)) hc mid hmid) rest hrest

theorem privateTerms_state {F M R : Type} [DecidableEq M] [SampleableType R]
    [AddCommMonoid R] [SMul F R]
    (p : M → Prop) (terms : List (M × F)) (cache : List (M × R))
    (ht : ∀ term ∈ terms, p term.1) (hc : ∀ entry ∈ cache, p entry.1)
    (out : R × List (M × R))
    (hout : out ∈ support ((simulateQ (privateListOracle (M := M) (R := R)) (evalTerms terms)).run cache)) :
    out.2.length ≤ cache.length + terms.length ∧ ∀ entry ∈ out.2, p entry.1 :=
  ⟨privateListRun_growth _ cache _ (evalTerms_queries terms) out hout,
    privateTerms_messages p terms cache ht hc out hout⟩

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [Q.HasProd] [Q.HasSum]
  {F G₁ G₂ M : Type} [Field F]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq M]
  {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ M M))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ M M cost).execute instr))
  (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)

/-- State validity survives the complete chronological preparation/evaluation
call, not just its individual private reads. -/
theorem evaluateTokens_state {value : Ty CryptoAtom}
    [SampleableType (value.Value (cryptoBase F G₁ G₂ M M))]
    [AddCommMonoid (value.Value (cryptoBase F G₁ G₂ M M))]
    [SMul F (value.Value (cryptoBase F G₁ G₂ M M))]
    (sampler : Code Q unifSpec iface rep.data.unit (rep.ty value))
    (fallback : Expr CryptoOp [message, cacheTy value] value)
    (hsample : sampler.denote () = ($ᵗ (value.Value (cryptoBase F G₁ G₂ M M)) : ProbComp _))
    (zero : Expr CryptoOp [.list evalRowTy, evalRowTy] value)
    (combine : Expr CryptoOp [value, scalar, value] value)
    (hz : ∀ rows default, zero.denote (arithmetic F G₁ G₂ M M cost) (rows, default, ()) = 0)
    (hcombine : ∀ answer coeff acc, combine.denote (arithmetic F G₁ G₂ M M cost) (answer, coeff, acc, ()) =
      acc + coeff • answer)
    (p : M → Prop) (tr : List (M × G₁)) (coeff : List F) (default : (M × G₁) × F)
    (cache : List (M × value.Value (cryptoBase F G₁ G₂ M M)))
    (ht : ∀ token ∈ tr, p token.1) (hc : ∀ entry ∈ cache, p entry.1)
    (out : Run (value.Value (cryptoBase F G₁ G₂ M M) × List (M × value.Value (cryptoBase F G₁ G₂ M M))))
    (hout : out ∈ support ((backendEvaluateTokens rep data cost primitive sampler fallback zero combine).run control queryCost ((tr, coeff, default, ()), cache))) :
    out.value.2.length ≤ cache.length + tr.length ∧ ∀ entry ∈ out.value.2, p entry.1 := by
  have h := Code.value_mem_denote control queryCost
    (backendEvaluateTokens rep data cost primitive sampler fallback zero combine)
    ((tr, coeff, default, ()), cache) out hout
  rw [backendEvaluateTokens, compileRead_denote rep data cost primitive sampler fallback hsample, evaluateTokens_source cost _ zero combine hz hcombine] at h
  have hk : ∀ term ∈ traceTerms coeff tr.reverse, p term.1 := by
    intro term hterm
    obtain ⟨n, hn, rfl⟩ := List.mem_mapIdx.mp hterm
    exact ht _ (List.mem_reverse.mp (List.getElem_mem hn))
  have hs := privateTerms_state p (traceTerms coeff tr.reverse) cache hk hc out.value h
  simpa only [traceTerms, List.length_mapIdx, List.length_reverse] using hs

end Signatures.Runtime.LazyAGM
