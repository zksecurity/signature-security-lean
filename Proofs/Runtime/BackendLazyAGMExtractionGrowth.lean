import Proofs.Runtime.BackendLazyAGMExtraction
import Proofs.Runtime.LazyAGMExtractionQueries

/-! Finite-cache growth for the actual native row evaluators and complete
extractors. These are semantic reachable-state bounds, separate from runtime
and stored-description certificates. No message-domain enumeration occurs. -/

open OracleComp OracleSpec PFunctor Model.LazyAGM BLS.LazyAGM.Reduction

namespace Signatures.Runtime.LazyAGM

open BackendProgram

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [Q.HasProd] [Q.HasSum]
  {F G₁ G₂ M : Type} [Field F] [SampleableType F]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq M]
  {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ M M))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ M M cost).execute instr))
  (sampling : MachineCompiler.SamplingImplementation Q iface rep)

theorem backendEvaluateGood_growth
    (rows : List ((M × G₁) × F)) (default : (M × G₁) × F) (cache : List (M × F))
    (out : F × List (M × F))
    (hout : out ∈ support ((backendEvaluateGood rep data cost primitive sampling).denote
      ((rows, default, ()), cache))) :
    out.2.length ≤ cache.length + rows.length := by
  rw [backendEvaluateGood_source] at hout
  simpa only [List.length_map] using privateListRun_growth _ cache _
    (evalTerms_queries (rows.map (fun row => (row.1.1, row.2)))) out hout

theorem backendEvaluateBad_growth
    (rows : List ((M × G₁) × F)) (default : (M × G₁) × F) (cache : List (M × (F × F)))
    (out : (F × F) × List (M × (F × F)))
    (hout : out ∈ support ((backendEvaluateBad rep data cost primitive sampling).denote
      ((rows, default, ()), cache))) :
    out.2.length ≤ cache.length + rows.length := by
  rw [backendEvaluateBad_source] at hout
  simpa only [List.length_map] using privateListRun_growth _ cache _
    (evalTerms_queries (rows.map (fun row => (row.1.1, row.2)))) out hout

theorem backendExtractGood_growth
    (output : (AGM.outputTy message).Value (cryptoBase F G₁ G₂ M M))
    (tr : Model.LazyAGM.Transcript M M G₁) (cache : List (M × F))
    (out : F × List (M × F))
    (hout : out ∈ support ((backendExtractGood rep data cost primitive sampling).denote
      ((output, tr, ()), cache))) :
    out.2.length ≤ cache.length + (tr.1.length + tr.2.length + 1) := by
  rw [backendExtractGood_source] at hout
  simpa only [chronological, List.length_reverse] using privateListRun_growth _ cache _
    (goodFinish_queries (AGM.outputView output) (chronological tr)) out hout

theorem backendExtractBad_growth
    (output : (AGM.outputTy message).Value (cryptoBase F G₁ G₂ M M))
    (tr : Model.LazyAGM.Transcript M M G₁) (cache : List (M × (F × F)))
    (out : F × List (M × (F × F)))
    (hout : out ∈ support ((backendExtractBad rep data cost primitive sampling).denote
      ((output, tr, ()), cache))) :
    out.2.length ≤ cache.length + (tr.2.length + 1) := by
  rw [backendExtractBad_source] at hout
  simpa only [chronological, List.length_reverse] using privateListRun_growth _ cache _
    (badFinish_queries (AGM.outputView output) (chronological tr)) out hout

end Signatures.Runtime.LazyAGM
