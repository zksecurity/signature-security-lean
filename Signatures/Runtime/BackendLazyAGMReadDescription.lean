import Signatures.Runtime.BackendLazyAGMRead

/-! Stored descriptions of the actual private extraction reads, including
their routing, fallback instructions, cache, and every sampler occurrence. -/

open OracleSpec PFunctor

namespace Signatures.Runtime.LazyAGM

open BackendProgram ReplySyntax

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {F G₁ G₂ M : Type} [Field F]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq M]
  {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ M M))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ M M cost).execute instr))
  (sizes : DescriptionSize Q) (allowance : Nat)
  (laws : LocalDescriptionLaws sizes allowance)
  (dataLaws : DataDescriptionLaws sizes rep.data data allowance)

include laws dataLaws

theorem backendRead_description {value : Ty CryptoAtom}
    (sampler : Code Q unifSpec iface rep.data.unit (rep.ty value))
    (fallback : Expr CryptoOp [message, cacheTy value] value) :
    (backendRead rep data cost primitive sampler fallback).descriptionSize sizes ≤
      sampler.descriptionSize sizes + sizes.localSize (primitive .messageEq) +
        Expression.descriptionBound allowance (fun instr => sizes.localSize (primitive instr)) fallback +
        288 * allowance + 36 := by
  have hi := laws.pair_bound (laws.fst (rep.ty message) (rep.ty (cacheTy value)))
    (laws.pair_bound (laws.snd (rep.ty message) (rep.ty (cacheTy value)))
      (dataLaws.unit (rep.ty (.pair message (cacheTy value)))))
  have ha := Expression.arguments_size rep data (arithmetic F G₁ G₂ M M cost) primitive
    sizes allowance laws dataLaws (fun instr => sizes.localSize (primitive instr))
    (fun _ => le_rfl) (readArgs fallback)
  have hp := laws.pair_bound ha (dataLaws.unit (rep.env [message, cacheTy value]))
  have hc := SampledCache.description rep data (arithmetic F G₁ G₂ M M cost) primitive
    rep.data.unit sampler CryptoOp.messageEq sizes allowance laws dataLaws
  have ho := laws.fst (rep.ty (cacheResultTy value)) rep.data.unit
  rw [backendRead]
  dsimp only [Code.descriptionSize, readFrame]
  simp only [readArgs, v0, v1, Expression.argumentsDescription,
    Expression.descriptionBound, Expression.variableDescription] at hp
  dsimp only [readArgs, v0, v1, cacheResultTy, cacheTy] at *
  omega

variable [SampleableType F]

theorem backendGoodRead_description (sampling : MachineCompiler.SamplingImplementation Q iface rep) :
    (backendGoodRead rep data cost primitive sampling).descriptionSize sizes ≤
      sampling.scalar.descriptionSize sizes + sizes.localSize (primitive .messageEq) +
        sizes.localSize (primitive .zero) + 300 * allowance + 40 := by
  rw [backendGoodRead]
  have h := backendRead_description rep data cost primitive sizes allowance laws dataLaws
    sampling.scalar (.op .zero .unit)
  simp only [Expression.descriptionBound] at h
  omega

theorem backendBadRead_description (sampling : MachineCompiler.SamplingImplementation Q iface rep) :
    (backendBadRead rep data cost primitive sampling).descriptionSize sizes ≤
      2 * sampling.scalar.descriptionSize sizes + sizes.localSize (primitive .messageEq) +
        2 * sizes.localSize (primitive .zero) + 320 * allowance + 48 := by
  rw [backendBadRead]
  have h := backendRead_description rep data cost primitive sizes allowance laws dataLaws
    (pairSampler rep data sampling) (.pair (.op .zero .unit) (.op .zero .unit))
  have hs := PairSampling.description rep.data data (rep.ty scalar) (rep.ty scalar)
    sampling.scalar sampling.scalar sizes allowance laws dataLaws
  change (pairSampler rep data sampling).descriptionSize sizes ≤ _ at hs
  simp only [Expression.descriptionBound] at h
  omega

end Signatures.Runtime.LazyAGM
