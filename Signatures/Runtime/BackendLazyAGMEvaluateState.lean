import Signatures.Runtime.BackendLazyAGMEvaluate

/-! Counter and private-cache invariants for actual native evaluator steps.
These facts are transported from exact source semantics to every supported
costed execution. They do not presume an iteration runtime bound. -/

open OracleComp OracleSpec PFunctor Model.LazyAGM BLS.LazyAGM.Reduction

namespace Signatures.Runtime.LazyAGM

open BackendProgram

def EvaluationRemaining {M R : Type} (valid : M → Prop)
    (rowCap cacheCap remaining : Nat) (state : (Nat × R) × List (M × R)) : Prop :=
  state.1.1 + remaining ≤ rowCap ∧ state.2.length + remaining ≤ cacheCap ∧
    ∀ entry ∈ state.2, valid entry.1

theorem privateRead_messages {M R : Type} [DecidableEq M] [SampleableType R]
    (p : M → Prop) (m : M) (cache : List (M × R))
    (hm : p m) (hc : ∀ entry ∈ cache, p entry.1)
    (out : R × List (M × R))
    (hout : out ∈ support (((privateListOracle (M := M) (R := R)) (.inr m)).run cache)) :
    ∀ entry ∈ out.2, p entry.1 := by
  rw [privateListOracle_lookup] at hout
  split at hout
  · simp only [support_pure, Set.mem_singleton_iff] at hout
    subst out
    exact hc
  · simp only [support_map, Set.mem_image] at hout
    obtain ⟨r, _, rfl⟩ := hout
    intro entry he
    rcases List.mem_cons.mp he with he | he
    · simpa only [he] using hm
    · exact hc entry he

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
  {value : Ty CryptoAtom} [SampleableType (value.Value (cryptoBase F G₁ G₂ M M))]
  (sampler : Code Q unifSpec iface rep.data.unit (rep.ty value))
  (fallback : Expr CryptoOp [message, cacheTy value] value)
  (hsample : sampler.denote () = ($ᵗ (value.Value (cryptoBase F G₁ G₂ M M)) : ProbComp _))

include hsample

theorem evalBody_source
    (combine : Expr CryptoOp [value, scalar, value] value)
    (n : Nat) (acc : value.Value (cryptoBase F G₁ G₂ M M))
    (rows : List ((M × G₁) × F)) (default : (M × G₁) × F)
    (cache : List (M × value.Value (cryptoBase F G₁ G₂ M M))) :
    (Language.compile rep data (arithmetic F G₁ G₂ M M cost) primitive
      (rep.ty (cacheTy value)) (readEffect rep data cost primitive sampler fallback)
      (evalBody combine)).denote (((n, acc), rows, default, ()), cache) =
      (fun p => ((n + 1, combine.denote (arithmetic F G₁ G₂ M M cost)
        (p.1, ((rows[n]?).getD default).2, acc, ())), p.2)) <$>
          ((privateListOracle (M := M) (R := value.Value (cryptoBase F G₁ G₂ M M)))
            (.inr ((rows[n]?).getD default).1.1)).run cache := by
  rw [compileRead_denote rep data cost primitive sampler fallback hsample, evalBody_denote cost]
  simp only [indexedStep, bind_pure_comp, StateT.run_map, Functor.map_map]
  rfl

theorem backendRead_state
    (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
    (p : M → Prop) (m : M) (cache : List (M × value.Value (cryptoBase F G₁ G₂ M M)))
    (hm : p m) (hc : ∀ entry ∈ cache, p entry.1)
    (out : Run (value.Value (cryptoBase F G₁ G₂ M M) × List (M × value.Value (cryptoBase F G₁ G₂ M M))))
    (hout : out ∈ support ((backendRead rep data cost primitive sampler fallback).run control queryCost (m, cache))) :
    out.value.2.length ≤ cache.length + 1 ∧ ∀ entry ∈ out.value.2, p entry.1 := by
  have h := Code.value_mem_denote control queryCost
    (backendRead rep data cost primitive sampler fallback) (m, cache) out hout
  rw [backendRead_denote rep data cost primitive sampler fallback hsample] at h
  exact ⟨privateListOracle_growth (.inr m) cache out.value h,
    privateRead_messages p m cache hm hc out.value h⟩

theorem evalBody_state
    (combine : Expr CryptoOp [value, scalar, value] value)
    (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
    (p : M → Prop) (n : Nat) (acc : value.Value (cryptoBase F G₁ G₂ M M))
    (rows : List ((M × G₁) × F)) (default : (M × G₁) × F)
    (cache : List (M × value.Value (cryptoBase F G₁ G₂ M M)))
    (hr : ∀ row ∈ rows, p row.1.1) (hd : p default.1.1) (hc : ∀ entry ∈ cache, p entry.1)
    (out : Run ((Nat × value.Value (cryptoBase F G₁ G₂ M M)) ×
      List (M × value.Value (cryptoBase F G₁ G₂ M M))))
    (hout : out ∈ support ((Language.compile rep data (arithmetic F G₁ G₂ M M cost) primitive
      (rep.ty (cacheTy value)) (readEffect rep data cost primitive sampler fallback)
      (evalBody combine)).run control queryCost (((n, acc), rows, default, ()), cache))) :
    out.value.1.1 = n + 1 ∧ out.value.2.length ≤ cache.length + 1 ∧
      ∀ entry ∈ out.value.2, p entry.1 := by
  have hm : p ((rows[n]?).getD default).1.1 := by
    cases hx : rows[n]? with
    | none => exact hd
    | some row => exact hr row (List.mem_of_getElem? hx)
  have h := Code.value_mem_denote control queryCost
    (Language.compile rep data (arithmetic F G₁ G₂ M M cost) primitive (rep.ty (cacheTy value))
      (readEffect rep data cost primitive sampler fallback) (evalBody combine))
    (((n, acc), rows, default, ()), cache) out hout
  rw [evalBody_source rep data cost primitive sampler fallback hsample] at h
  simp only [support_map, Set.mem_image] at h
  obtain ⟨r, hr', he⟩ := h
  rw [← he]
  exact ⟨rfl, privateListOracle_growth (.inr ((rows[n]?).getD default).1.1) cache r hr',
    privateRead_messages p _ cache hm hc r hr'⟩

theorem evalBody_remaining
    (combine : Expr CryptoOp [value, scalar, value] value)
    (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
    (p : M → Prop) (rowCap cacheCap remaining n : Nat)
    (acc : value.Value (cryptoBase F G₁ G₂ M M))
    (rows : List ((M × G₁) × F)) (default : (M × G₁) × F)
    (cache : List (M × value.Value (cryptoBase F G₁ G₂ M M)))
    (hr : ∀ row ∈ rows, p row.1.1) (hd : p default.1.1)
    (hi : EvaluationRemaining p rowCap cacheCap (remaining + 1) ((n, acc), cache))
    (out : Run ((Nat × value.Value (cryptoBase F G₁ G₂ M M)) ×
      List (M × value.Value (cryptoBase F G₁ G₂ M M))))
    (hout : out ∈ support ((Language.compile rep data (arithmetic F G₁ G₂ M M cost) primitive
      (rep.ty (cacheTy value)) (readEffect rep data cost primitive sampler fallback)
      (evalBody combine)).run control queryCost (((n, acc), rows, default, ()), cache))) :
    EvaluationRemaining p rowCap cacheCap remaining out.value := by
  have h := evalBody_state rep data cost primitive sampler fallback hsample combine control queryCost
    p n acc rows default cache hr hd hi.2.2 out hout
  refine ⟨?_, ?_, h.2.2⟩
  · have hn := hi.1
    dsimp only at hn
    rw [h.1]
    omega
  · have hc := hi.2.1
    have hg := h.2.1
    dsimp only at hc
    omega

end Signatures.Runtime.LazyAGM
