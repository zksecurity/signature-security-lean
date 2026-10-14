import Signatures.Runtime.BackendLazyAGMEvaluate
import Signatures.Runtime.LazyAGMExtraction

/-! Actual common-backend good/bad lazy BLS AGM extractors. The typed programs
construct chronological rows, run their cache evaluations, access the target,
and execute field extraction. The joint laws below do not substitute for the
remaining complete runtime and general-caller composition certificates. -/

open OracleComp OracleSpec PFunctor Model.LazyAGM

namespace Signatures.Runtime.LazyAGM

open BackendProgram

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {F G₁ G₂ M : Type} [Field F] [SampleableType F]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq M]
  {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ M M))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ M M cost).execute instr))
  (samplingCode : MachineCompiler.SamplingImplementation Q iface rep)

@[irreducible] def backendEvaluateTokens {value : Ty CryptoAtom}
    (sampler : Code Q unifSpec iface rep.data.unit (rep.ty value))
    (fallback : Expr CryptoOp [message, cacheTy value] value)
    (zero : Expr CryptoOp [.list evalRowTy, evalRowTy] value)
    (combine : Expr CryptoOp [value, scalar, value] value) :
    Code Q unifSpec iface
      (StepClass.HasProd.prod (rep.env [.list (AGM.tokenTy message), .list scalar, evalRowTy])
        (rep.ty (cacheTy value)))
      (rep.ty (.pair value (cacheTy value))) :=
  Language.compile rep data (arithmetic F G₁ G₂ M M cost) primitive (rep.ty (cacheTy value))
    (readEffect rep data cost primitive sampler fallback) (evaluateTokens zero combine)

@[irreducible] def backendExtractGood :
    Code Q unifSpec iface
      (StepClass.HasProd.prod (rep.env [AGM.outputTy message, transcriptTy]) (rep.ty (cacheTy scalar)))
      (rep.ty (.pair scalar (cacheTy scalar))) :=
  Language.compile rep data (arithmetic F G₁ G₂ M M cost) primitive (rep.ty (cacheTy scalar))
    (readEffect rep data cost primitive samplingCode.scalar (.op .zero .unit)) extractGood

@[irreducible] def backendExtractBad :
    Code Q unifSpec iface
      (StepClass.HasProd.prod (rep.env [AGM.outputTy message, transcriptTy]) (rep.ty (cacheTy (.pair scalar scalar))))
      (rep.ty (.pair scalar (cacheTy (.pair scalar scalar)))) :=
  Language.compile rep data (arithmetic F G₁ G₂ M M cost) primitive (rep.ty (cacheTy (.pair scalar scalar)))
    (readEffect rep data cost primitive (pairSampler rep data samplingCode)
      (.pair (.op .zero .unit) (.op .zero .unit))) extractBad

theorem backendExtractGood_source
    (out : (AGM.outputTy message).Value (cryptoBase F G₁ G₂ M M))
    (tr : Model.LazyAGM.Transcript M M G₁) (cache : List (M × F)) :
    (backendExtractGood rep data cost primitive samplingCode).denote ((out, tr, ()), cache) =
      (simulateQ (BLS.LazyAGM.Reduction.privateListOracle (M := M) (R := F))
        (goodFinish (AGM.outputView out) (chronological tr))).run cache := by
  rw [backendExtractGood, compileRead_denote rep data cost primitive samplingCode.scalar (.op .zero .unit)
    (samplingCode.scalar_denote ()), extractGood_source]

theorem backendExtractBad_source
    (out : (AGM.outputTy message).Value (cryptoBase F G₁ G₂ M M))
    (tr : Model.LazyAGM.Transcript M M G₁) (cache : List (M × (F × F))) :
    (backendExtractBad rep data cost primitive samplingCode).denote ((out, tr, ()), cache) =
      (simulateQ (BLS.LazyAGM.Reduction.privateListOracle (M := M) (R := F × F))
        (badFinish (AGM.outputView out) (chronological tr))).run cache := by
  rw [backendExtractBad, compileRead_denote rep data cost primitive (pairSampler rep data samplingCode)
    (.pair (.op .zero .unit) (.op .zero .unit)) (pairSampler_denote rep data samplingCode ()), extractBad_source]

end Signatures.Runtime.LazyAGM
