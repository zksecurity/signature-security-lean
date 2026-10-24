import Proofs.Runtime.BackendWeightedExtraction
import Proofs.Runtime.WeightedExtractionState
import Proofs.Runtime.BackendWeightedSignInputs

/-! Native extraction preserves cached bindings and encountered-key predicates.
For a valid transcript, only the final message can grow the private cache, by
at most degree/dimension + 1 entries. The input transcript is the simulator's
reverse log; the proof explicitly uses its chronological source view. -/

open OracleComp OracleSpec PFunctor Model.LazyAGM
open Model.LazyAGM.WeightedReduction

namespace Signatures.Runtime.WeightedAGM.Extract

open BackendProgram

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {F G₁ G₂ K M : Type} [Field F] [SampleableType F]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq K] [DecidableEq M]
  {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  (sampling : MachineCompiler.SamplingImplementation Q iface rep) (index : Index)
  (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)

theorem backendGood_cache
    (p : index.ty.Value (cryptoBase F G₁ G₂ K M) → Prop)
    (out : (AGM.outputTy index.messageTy).Value (cryptoBase F G₁ G₂ K M))
    (tr : Model.LazyAGM.Transcript (index.ty.Value (cryptoBase F G₁ G₂ K M))
      (index.messageTy.Value (cryptoBase F G₁ G₂ K M)) G₁)
    (cache : List (index.ty.Value (cryptoBase F G₁ G₂ K M) × F))
    (hc : TranscriptCached (index.sourceTerms cost) (Reply.chronological tr) cache)
    (hk : ∀ entry ∈ cache, p entry.1)
    (ht : ∀ row ∈ index.sourceTerms cost out.1, p row.1)
    (z : Run (F × List (index.ty.Value (cryptoBase F G₁ G₂ K M) × F)))
    (hz : z ∈ support ((backendGood rep data cost primitive sampling index).run
      control queryCost ((out, tr, ()), cache))) :
    CacheExtends cache z.value.2 ∧ TermsCached (index.sourceTerms cost out.1) z.value.2 ∧
      z.value.2.length ≤ cache.length + (index.bound + 1) ∧ ∀ entry ∈ z.value.2, p entry.1 := by
  have h := Code.value_mem_denote control queryCost (backendGood rep data cost primitive sampling index)
    ((out, tr, ()), cache) z hz
  rw [backendGood_source] at h
  have hs := goodFinish_cache p (index.sourceTerms cost) (AGM.outputView out)
    (Reply.chronological tr) cache hc hk ht z.value h
  simpa only [AGM.outputView, Index.terms_length] using hs

theorem backendBad_cache
    (p : index.ty.Value (cryptoBase F G₁ G₂ K M) → Prop)
    (out : (AGM.outputTy index.messageTy).Value (cryptoBase F G₁ G₂ K M))
    (tr : Model.LazyAGM.Transcript (index.ty.Value (cryptoBase F G₁ G₂ K M))
      (index.messageTy.Value (cryptoBase F G₁ G₂ K M)) G₁)
    (cache : List (index.ty.Value (cryptoBase F G₁ G₂ K M) × (F × F)))
    (hc : TranscriptCached (index.sourceTerms cost) (Reply.chronological tr) cache)
    (hk : ∀ entry ∈ cache, p entry.1)
    (ht : ∀ row ∈ index.sourceTerms cost out.1, p row.1)
    (z : Run (F × List (index.ty.Value (cryptoBase F G₁ G₂ K M) × (F × F))))
    (hz : z ∈ support ((backendBad rep data cost primitive sampling index).run
      control queryCost ((out, tr, ()), cache))) :
    CacheExtends cache z.value.2 ∧ TermsCached (index.sourceTerms cost out.1) z.value.2 ∧
      z.value.2.length ≤ cache.length + (index.bound + 1) ∧ ∀ entry ∈ z.value.2, p entry.1 := by
  have h := Code.value_mem_denote control queryCost (backendBad rep data cost primitive sampling index)
    ((out, tr, ()), cache) z hz
  rw [backendBad_source] at h
  have hs := badFinish_cache p (index.sourceTerms cost) (AGM.outputView out)
    (Reply.chronological tr) cache hc hk ht z.value h
  simpa only [AGM.outputView, Index.terms_length] using hs

end Signatures.Runtime.WeightedAGM.Extract
