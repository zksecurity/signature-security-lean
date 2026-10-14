import Signatures.Runtime.BackendWeightedExtraction
import Signatures.Runtime.WeightedExtractionDescription
import Signatures.Runtime.BackendWeightedReplyDescription

/-! Complete stored-code bounds for actual weighted extractors. No finished
extractor description is assumed, and no finite topic/slot domain is required. -/

open OracleSpec PFunctor

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
  (sizes : DescriptionSize Q) (allowance : Nat) (laws : LocalDescriptionLaws sizes allowance)
  (dataLaws : DataDescriptionLaws sizes rep.data data allowance)

include laws dataLaws

theorem backendGood_description :
    (backendGood rep data cost primitive sampling index).descriptionSize sizes ≤
      3 * sampling.scalar.descriptionSize sizes + 3 * sizes.localSize (primitive .keyEq) +
      6 * sizes.localSize (primitive (.finVal index.bound)) +
      9 * sizes.localSize (primitive .zero) + 4 * sizes.localSize (primitive .add) +
      5 * sizes.localSize (primitive .mul) + 8 * sizes.localSize (primitive .natEq) +
      5 * sizes.localSize (primitive .natSub) + 8 * sizes.localSize (primitive .natAdd) +
      sizes.localSize (primitive .one) + sizes.localSize (primitive (.finZero index.bound)) +
      sizes.localSize (primitive .sub) + sizes.localSize (primitive .div) +
      2 * index.termsDescription allowance (fun instr => sizes.localSize (primitive instr)) +
      10000 * allowance + 640 := by
  let reader := Read.goodRead rep data cost primitive sampling index
  have hr := Read.goodRead_description rep data cost primitive sizes allowance laws dataLaws sampling index
  have ht := Index.terms_description allowance (fun instr => sizes.localSize (primitive instr)) index
  have hd := Index.default_description allowance (fun instr => sizes.localSize (primitive instr)) index
  have h := Language.compile_descriptionSize sizes allowance laws rep data
    (arithmetic F G₁ G₂ K M cost) primitive dataLaws
    (fun instr => sizes.localSize (primitive instr)) (fun _ => le_rfl)
    (rep.ty (Reply.cacheTy index.ty scalar)) (readEffect rep reader)
    (fun _ => reader.descriptionSize sizes) (fun instr => by cases instr; rfl)
    (good index.terms index.defaultTerm)
  have hs := good_description allowance (fun instr => sizes.localSize (primitive instr))
    (reader.descriptionSize sizes) index.terms index.defaultTerm
  rw [backendGood]
  exact h.trans (hs.trans (by dsimp only [reader] at *; omega))

theorem backendBad_description :
    (backendBad rep data cost primitive sampling index).descriptionSize sizes ≤
      4 * sampling.scalar.descriptionSize sizes + 2 * sizes.localSize (primitive .keyEq) +
      4 * sizes.localSize (primitive (.finVal index.bound)) +
      10 * sizes.localSize (primitive .zero) + 4 * sizes.localSize (primitive .add) +
      5 * sizes.localSize (primitive .mul) + 5 * sizes.localSize (primitive .natEq) +
      3 * sizes.localSize (primitive .natSub) + 5 * sizes.localSize (primitive .natAdd) +
      sizes.localSize (primitive (.finZero index.bound)) + 2 * sizes.localSize (primitive .sub) +
      sizes.localSize (primitive .neg) + sizes.localSize (primitive .div) +
      2 * index.termsDescription allowance (fun instr => sizes.localSize (primitive instr)) +
      10000 * allowance + 640 := by
  let reader := Read.badRead rep data cost primitive sampling index
  have hr := Read.badRead_description rep data cost primitive sizes allowance laws dataLaws sampling index
  have ht := Index.terms_description allowance (fun instr => sizes.localSize (primitive instr)) index
  have hd := Index.default_description allowance (fun instr => sizes.localSize (primitive instr)) index
  have h := Language.compile_descriptionSize sizes allowance laws rep data
    (arithmetic F G₁ G₂ K M cost) primitive dataLaws
    (fun instr => sizes.localSize (primitive instr)) (fun _ => le_rfl)
    (rep.ty (Reply.cacheTy index.ty (.pair scalar scalar))) (readEffect rep reader)
    (fun _ => reader.descriptionSize sizes) (fun instr => by cases instr; rfl)
    (bad index.terms index.defaultTerm)
  have hs := bad_description allowance (fun instr => sizes.localSize (primitive instr))
    (reader.descriptionSize sizes) index.terms index.defaultTerm
  rw [backendBad]
  exact h.trans (hs.trans (by dsimp only [reader] at *; omega))

end Signatures.Runtime.WeightedAGM.Extract
