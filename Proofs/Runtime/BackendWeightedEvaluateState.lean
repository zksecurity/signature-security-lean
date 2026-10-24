import Proofs.Runtime.BackendWeightedEvaluate
import Proofs.Runtime.BackendLazyAGMEvaluateState

/-! Counter and private-cache invariants for actual native evaluator steps.
These facts are transported from exact source semantics to every supported
costed execution. They do not presume an iteration runtime bound. -/

open OracleComp OracleSpec PFunctor Model.LazyAGM BLS.LazyAGM.Reduction

namespace Signatures.Runtime.WeightedAGM.Evaluate

open BackendProgram Read

open LazyAGM (EvaluationRemaining privateRead_messages)

variable {indexTy : Ty CryptoAtom}

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [Q.HasProd] [Q.HasSum]
  {F G₁ G₂ K M : Type} [Field F]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq K] [DecidableEq M]
  {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  {value : Ty CryptoAtom} [SampleableType (value.Value (cryptoBase F G₁ G₂ K M))]
  [DecidableEq (indexTy.Value (cryptoBase F G₁ G₂ K M))]
  (reader : Code Q unifSpec iface (rep.ty (inputTy indexTy value))
    (rep.ty (.pair value (cacheTy indexTy value))))
  (hreader : ∀ k cache, reader.denote (k, cache) =
    ((privateListOracle (M := indexTy.Value (cryptoBase F G₁ G₂ K M))
      (R := value.Value (cryptoBase F G₁ G₂ K M))) (.inr k)).run cache)

include hreader

theorem compileRead_denote {Γ : List (Ty CryptoAtom)} {result : Ty CryptoAtom}
    (program : Program CryptoOp (EvalCmd indexTy value) Γ result)
    (env : Env (cryptoBase F G₁ G₂ K M) Γ)
    (cache : List (indexTy.Value (cryptoBase F G₁ G₂ K M) × value.Value (cryptoBase F G₁ G₂ K M))) :
    (Language.compile rep data (arithmetic F G₁ G₂ K M cost) primitive (rep.ty (cacheTy indexTy value))
      (readEffect rep reader) program).denote (env, cache) =
      (program.denote (arithmetic F G₁ G₂ K M cost)
        (evalSemantics (fun k => privateListOracle (.inr k))) env).run cache := by
  apply Language.compile_denote
  intro a b instr input saved
  cases instr
  exact hreader input saved

theorem evalBody_source
    (combine : Expr CryptoOp [value, scalar, value] value)
    (n : Nat) (acc : value.Value (cryptoBase F G₁ G₂ K M))
    (rows : List (indexTy.Value (cryptoBase F G₁ G₂ K M) × F)) (default : indexTy.Value (cryptoBase F G₁ G₂ K M) × F)
    (cache : List (indexTy.Value (cryptoBase F G₁ G₂ K M) × value.Value (cryptoBase F G₁ G₂ K M))) :
    (Language.compile rep data (arithmetic F G₁ G₂ K M cost) primitive
      (rep.ty (cacheTy indexTy value)) (readEffect rep reader)
      (evalBody combine)).denote (((n, acc), rows, default, ()), cache) =
      (fun p => ((n + 1, combine.denote (arithmetic F G₁ G₂ K M cost)
        (p.1, ((rows[n]?).getD default).2, acc, ())), p.2)) <$>
          ((privateListOracle (M := indexTy.Value (cryptoBase F G₁ G₂ K M)) (R := value.Value (cryptoBase F G₁ G₂ K M)))
            (.inr ((rows[n]?).getD default).1)).run cache := by
  rw [compileRead_denote rep data cost primitive reader hreader, evalBody_denote cost]
  simp only [indexedStep, bind_pure_comp, StateT.run_map, Functor.map_map]
  rfl

omit [Q.HasCategory] [Q.HasProd] [Q.HasSum] [Field F] [DecidableEq F]
  [DecidableEq G₁] [DecidableEq G₂] [AddCommGroup G₁] [Module F G₁]
  [AddCommGroup G₂] [Module F G₂] [DecidableEq K] [DecidableEq M] in
theorem backendRead_state
    (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
    (p : indexTy.Value (cryptoBase F G₁ G₂ K M) → Prop) (m : indexTy.Value (cryptoBase F G₁ G₂ K M)) (cache : List (indexTy.Value (cryptoBase F G₁ G₂ K M) × value.Value (cryptoBase F G₁ G₂ K M)))
    (hm : p m) (hc : ∀ entry ∈ cache, p entry.1)
    (out : Run (value.Value (cryptoBase F G₁ G₂ K M) × List (indexTy.Value (cryptoBase F G₁ G₂ K M) × value.Value (cryptoBase F G₁ G₂ K M))))
    (hout : out ∈ support ((reader).run control queryCost (m, cache))) :
    out.value.2.length ≤ cache.length + 1 ∧ ∀ entry ∈ out.value.2, p entry.1 := by
  have h := Code.value_mem_denote control queryCost
    (reader) (m, cache) out hout
  rw [hreader] at h
  exact ⟨privateListOracle_growth (.inr m) cache out.value h,
    privateRead_messages p m cache hm hc out.value h⟩

theorem evalBody_state
    (combine : Expr CryptoOp [value, scalar, value] value)
    (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
    (p : indexTy.Value (cryptoBase F G₁ G₂ K M) → Prop) (n : Nat) (acc : value.Value (cryptoBase F G₁ G₂ K M))
    (rows : List (indexTy.Value (cryptoBase F G₁ G₂ K M) × F)) (default : indexTy.Value (cryptoBase F G₁ G₂ K M) × F)
    (cache : List (indexTy.Value (cryptoBase F G₁ G₂ K M) × value.Value (cryptoBase F G₁ G₂ K M)))
    (hr : ∀ row ∈ rows, p row.1) (hd : p default.1) (hc : ∀ entry ∈ cache, p entry.1)
    (out : Run ((Nat × value.Value (cryptoBase F G₁ G₂ K M)) ×
      List (indexTy.Value (cryptoBase F G₁ G₂ K M) × value.Value (cryptoBase F G₁ G₂ K M))))
    (hout : out ∈ support ((Language.compile rep data (arithmetic F G₁ G₂ K M cost) primitive
      (rep.ty (cacheTy indexTy value)) (readEffect rep reader)
      (evalBody combine)).run control queryCost (((n, acc), rows, default, ()), cache))) :
    out.value.1.1 = n + 1 ∧ out.value.2.length ≤ cache.length + 1 ∧
      ∀ entry ∈ out.value.2, p entry.1 := by
  have hm : p ((rows[n]?).getD default).1 := by
    cases hx : rows[n]? with
    | none => exact hd
    | some row => exact hr row (List.mem_of_getElem? hx)
  have h := Code.value_mem_denote control queryCost
    (Language.compile rep data (arithmetic F G₁ G₂ K M cost) primitive (rep.ty (cacheTy indexTy value))
      (readEffect rep reader) (evalBody combine))
    (((n, acc), rows, default, ()), cache) out hout
  rw [evalBody_source rep data cost primitive reader hreader] at h
  simp only [support_map, Set.mem_image] at h
  obtain ⟨r, hr', he⟩ := h
  rw [← he]
  exact ⟨rfl, privateListOracle_growth (.inr ((rows[n]?).getD default).1) cache r hr',
    privateRead_messages p _ cache hm hc r hr'⟩

theorem evalBody_remaining
    (combine : Expr CryptoOp [value, scalar, value] value)
    (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
    (p : indexTy.Value (cryptoBase F G₁ G₂ K M) → Prop) (rowCap cacheCap remaining n : Nat)
    (acc : value.Value (cryptoBase F G₁ G₂ K M))
    (rows : List (indexTy.Value (cryptoBase F G₁ G₂ K M) × F)) (default : indexTy.Value (cryptoBase F G₁ G₂ K M) × F)
    (cache : List (indexTy.Value (cryptoBase F G₁ G₂ K M) × value.Value (cryptoBase F G₁ G₂ K M)))
    (hr : ∀ row ∈ rows, p row.1) (hd : p default.1)
    (hi : EvaluationRemaining p rowCap cacheCap (remaining + 1) ((n, acc), cache))
    (out : Run ((Nat × value.Value (cryptoBase F G₁ G₂ K M)) ×
      List (indexTy.Value (cryptoBase F G₁ G₂ K M) × value.Value (cryptoBase F G₁ G₂ K M))))
    (hout : out ∈ support ((Language.compile rep data (arithmetic F G₁ G₂ K M cost) primitive
      (rep.ty (cacheTy indexTy value)) (readEffect rep reader)
      (evalBody combine)).run control queryCost (((n, acc), rows, default, ()), cache))) :
    EvaluationRemaining p rowCap cacheCap remaining out.value := by
  have h := evalBody_state rep data cost primitive reader hreader combine control queryCost
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

end Signatures.Runtime.WeightedAGM.Evaluate
