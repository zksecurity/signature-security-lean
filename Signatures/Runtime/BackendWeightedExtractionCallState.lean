import Signatures.Runtime.BackendWeightedEvaluateState
import Signatures.Runtime.WeightedExtraction
import Signatures.Runtime.WeightedExtractionState

/-! Intermediate extraction calls preserve all cached bindings. Transcript
calls retain the exact cache when their bases were cached by the interaction;
only final-target terms may add entries. These facts apply to supported native
runs and impose no runtime or finite-domain premise. -/

open OracleComp OracleSpec PFunctor Model.LazyAGM
open Model.LazyAGM.WeightedReduction BLS.LazyAGM.Reduction

namespace Signatures.Runtime.WeightedAGM.Extract

open BackendProgram Evaluate

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
  (reader : Code Q unifSpec iface (rep.ty (Read.inputTy indexTy value))
    (rep.ty (.pair value (Read.cacheTy indexTy value))))
  (hreader : ∀ k cache, reader.denote (k, cache) =
    ((privateListOracle (M := indexTy.Value (cryptoBase F G₁ G₂ K M))
      (R := value.Value (cryptoBase F G₁ G₂ K M))) (.inr k)).run cache)

variable [AddCommMonoid (value.Value (cryptoBase F G₁ G₂ K M))]
  [SMul F (value.Value (cryptoBase F G₁ G₂ K M))]
  (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)

include hreader

attribute [local irreducible] Language.compile Expression.compile Expression.arguments

theorem evaluateCoefficients_cached {messageTy : Ty CryptoAtom}
    (terms : Expr CryptoOp [messageTy] (.list (Terms.termTy indexTy)))
    (zero : Expr CryptoOp [.list (evalRowTy indexTy), evalRowTy indexTy] value)
    (combine : Expr CryptoOp [value, scalar, value] value)
    (hz : ∀ rows default, zero.denote (arithmetic F G₁ G₂ K M cost) (rows, default, ()) = 0)
    (hcombine : ∀ answer coeff acc, combine.denote (arithmetic F G₁ G₂ K M cost) (answer, coeff, acc, ()) =
      acc + coeff • answer)
    (tr : List (messageTy.Value (cryptoBase F G₁ G₂ K M) × G₁)) (coeff : List F)
    (default : indexTy.Value (cryptoBase F G₁ G₂ K M) × F)
    (cache : List (indexTy.Value (cryptoBase F G₁ G₂ K M) × value.Value (cryptoBase F G₁ G₂ K M)))
    (hc : TermsCached (Model.LazyAGM.WeightedReduction.signedTerms
      (fun m => terms.denote (arithmetic F G₁ G₂ K M cost) (m, ())) coeff tr.reverse) cache)
    (out : Run (value.Value (cryptoBase F G₁ G₂ K M) ×
      List (indexTy.Value (cryptoBase F G₁ G₂ K M) × value.Value (cryptoBase F G₁ G₂ K M))))
    (hout : out ∈ support ((Language.compile rep data (arithmetic F G₁ G₂ K M cost) primitive
      (rep.ty (Read.cacheTy indexTy value)) (readEffect rep reader)
      (evaluateCoefficients terms zero combine)).run control queryCost ((tr, coeff, default, ()), cache))) :
    out.value.2 = cache := by
  have h := Code.value_mem_denote control queryCost _ _ out hout
  rw [compileRead_denote rep data cost primitive reader hreader,
    evaluateCoefficients_source cost (privateListOracle (M := indexTy.Value (cryptoBase F G₁ G₂ K M))
      (R := value.Value (cryptoBase F G₁ G₂ K M))) terms zero combine hz hcombine,
    evalTerms_cached_eq _ cache hc] at h
  simp only [support_pure, Set.mem_singleton_iff] at h
  exact congrArg Prod.snd h

theorem evaluateTarget_cache {messageTy : Ty CryptoAtom}
    (terms : Expr CryptoOp [messageTy] (.list (Terms.termTy indexTy)))
    (zero : Expr CryptoOp [.list (evalRowTy indexTy), evalRowTy indexTy] value)
    (combine : Expr CryptoOp [value, scalar, value] value)
    (hz : ∀ rows default, zero.denote (arithmetic F G₁ G₂ K M cost) (rows, default, ()) = 0)
    (hcombine : ∀ answer coeff acc, combine.denote (arithmetic F G₁ G₂ K M cost) (answer, coeff, acc, ()) =
      acc + coeff • answer)
    (p : indexTy.Value (cryptoBase F G₁ G₂ K M) → Prop)
    (m : messageTy.Value (cryptoBase F G₁ G₂ K M))
    (default : indexTy.Value (cryptoBase F G₁ G₂ K M) × F)
    (cache : List (indexTy.Value (cryptoBase F G₁ G₂ K M) × value.Value (cryptoBase F G₁ G₂ K M)))
    (ht : ∀ row ∈ terms.denote (arithmetic F G₁ G₂ K M cost) (m, ()), p row.1)
    (hc : ∀ entry ∈ cache, p entry.1)
    (out : Run (value.Value (cryptoBase F G₁ G₂ K M) ×
      List (indexTy.Value (cryptoBase F G₁ G₂ K M) × value.Value (cryptoBase F G₁ G₂ K M))))
    (hout : out ∈ support ((Language.compile rep data (arithmetic F G₁ G₂ K M cost) primitive
      (rep.ty (Read.cacheTy indexTy value)) (readEffect rep reader)
      (evaluateTarget terms zero combine)).run control queryCost ((m, default, ()), cache))) :
    CacheExtends cache out.value.2 ∧
      TermsCached (terms.denote (arithmetic F G₁ G₂ K M cost) (m, ())) out.value.2 ∧
      out.value.2.length ≤ cache.length + (terms.denote (arithmetic F G₁ G₂ K M cost) (m, ())).length ∧
      ∀ entry ∈ out.value.2, p entry.1 := by
  have h := Code.value_mem_denote control queryCost _ _ out hout
  rw [compileRead_denote rep data cost primitive reader hreader,
    evaluateTarget_source cost (privateListOracle (M := indexTy.Value (cryptoBase F G₁ G₂ K M))
      (R := value.Value (cryptoBase F G₁ G₂ K M))) terms zero combine hz hcombine] at h
  obtain ⟨he, hcached, hlength⟩ := evalTerms_list_preserves _ cache out.value h
  exact ⟨he, hcached, hlength, LazyAGM.privateTerms_messages p _ cache ht hc out.value h⟩

end Signatures.Runtime.WeightedAGM.Extract
