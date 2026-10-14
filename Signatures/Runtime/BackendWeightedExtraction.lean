import Signatures.Runtime.WeightedExtraction
import Signatures.Runtime.BackendWeightedReplySemantics

/-! Native OOPS/Proximity extractors. The compiled programs execute coefficient
matching, weighted term construction, all private reads, and final field
arithmetic. Their laws preserve the joint output/cache distribution, including
unseen final targets and the source's division-by-zero behavior. -/

open OracleComp OracleSpec PFunctor Model.LazyAGM

namespace Signatures.Runtime.WeightedAGM.Extract

open BackendProgram Evaluate

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

@[irreducible] def backendGood : Code Q unifSpec iface
    (StepClass.HasProd.prod (rep.env [AGM.outputTy index.messageTy, Reply.transcriptTy index.ty index.messageTy])
      (rep.ty (Reply.cacheTy index.ty scalar)))
    (rep.ty (Reply.cacheResultTy index.ty scalar)) :=
  Language.compile rep data (arithmetic F G₁ G₂ K M cost) primitive
    (rep.ty (Reply.cacheTy index.ty scalar))
    (readEffect rep (Read.goodRead rep data cost primitive sampling index))
    (good index.terms index.defaultTerm)

@[irreducible] def backendBad : Code Q unifSpec iface
    (StepClass.HasProd.prod (rep.env [AGM.outputTy index.messageTy, Reply.transcriptTy index.ty index.messageTy])
      (rep.ty (Reply.cacheTy index.ty (.pair scalar scalar))))
    (rep.ty (.pair scalar (Reply.cacheTy index.ty (.pair scalar scalar)))) :=
  Language.compile rep data (arithmetic F G₁ G₂ K M cost) primitive
    (rep.ty (Reply.cacheTy index.ty (.pair scalar scalar)))
    (readEffect rep (Read.badRead rep data cost primitive sampling index))
    (bad index.terms index.defaultTerm)

theorem backendGood_source
    (out : (AGM.outputTy index.messageTy).Value (cryptoBase F G₁ G₂ K M))
    (tr : Model.LazyAGM.Transcript (index.ty.Value (cryptoBase F G₁ G₂ K M))
      (index.messageTy.Value (cryptoBase F G₁ G₂ K M)) G₁)
    (cache : List (index.ty.Value (cryptoBase F G₁ G₂ K M) × F)) :
    (backendGood rep data cost primitive sampling index).denote ((out, tr, ()), cache) =
      (simulateQ (BLS.LazyAGM.Reduction.privateListOracle
        (M := index.ty.Value (cryptoBase F G₁ G₂ K M)) (R := F))
        (goodFinish (index.sourceTerms cost) (AGM.outputView out) (Reply.chronological tr))).run cache := by
  let impl := BLS.LazyAGM.Reduction.privateListOracle
    (M := index.ty.Value (cryptoBase F G₁ G₂ K M)) (R := F)
  have h := Language.compile_denote rep data (arithmetic F G₁ G₂ K M cost) primitive
    (rep.ty (Reply.cacheTy index.ty scalar))
    (readEffect rep (Read.goodRead rep data cost primitive sampling index))
    (evalSemantics (fun k => impl (.inr k)))
    (by intro a b instr input saved; cases instr
        exact Read.goodRead_denote rep data cost primitive sampling index input saved)
    (good index.terms index.defaultTerm) (out, tr, ()) cache
  rw [backendGood, h, good_source]
  rfl

theorem backendBad_source
    (out : (AGM.outputTy index.messageTy).Value (cryptoBase F G₁ G₂ K M))
    (tr : Model.LazyAGM.Transcript (index.ty.Value (cryptoBase F G₁ G₂ K M))
      (index.messageTy.Value (cryptoBase F G₁ G₂ K M)) G₁)
    (cache : List (index.ty.Value (cryptoBase F G₁ G₂ K M) × (F × F))) :
    (backendBad rep data cost primitive sampling index).denote ((out, tr, ()), cache) =
      (simulateQ (BLS.LazyAGM.Reduction.privateListOracle
        (M := index.ty.Value (cryptoBase F G₁ G₂ K M)) (R := F × F))
        (badFinish (index.sourceTerms cost) (AGM.outputView out) (Reply.chronological tr))).run cache := by
  let impl := BLS.LazyAGM.Reduction.privateListOracle
    (M := index.ty.Value (cryptoBase F G₁ G₂ K M)) (R := F × F)
  have h := Language.compile_denote rep data (arithmetic F G₁ G₂ K M cost) primitive
    (rep.ty (Reply.cacheTy index.ty (.pair scalar scalar)))
    (readEffect rep (Read.badRead rep data cost primitive sampling index))
    (evalSemantics (fun k => impl (.inr k)))
    (by intro a b instr input saved; cases instr
        exact Read.badRead_denote rep data cost primitive sampling index input saved)
    (bad index.terms index.defaultTerm) (out, tr, ()) cache
  rw [backendBad, h, bad_source]
  rfl

end Signatures.Runtime.WeightedAGM.Extract
