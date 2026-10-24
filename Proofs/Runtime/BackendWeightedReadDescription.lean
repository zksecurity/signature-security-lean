import Proofs.Runtime.BackendWeightedRead

/-! Stored-code bounds for native weighted private reads. These include the
fallback instructions, comparison implementation, both sampler occurrences in
the pair branch, and all argument/state adapters. -/

open OracleSpec PFunctor

namespace Signatures.Runtime.WeightedAGM.Read

open BackendProgram

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  (sizes : DescriptionSize Q) (allowance : Nat)
  (laws : LocalDescriptionLaws sizes allowance)
  (dataLaws : DataDescriptionLaws sizes rep.data data allowance)

include laws dataLaws

theorem zeroCode_description (input : Ty CryptoAtom) :
    sizes.localSize (zeroCode rep data cost primitive input) ≤ sizes.localSize (primitive .zero) + 2 * allowance := by
  rw [zeroCode, DescriptionSize.castFunction]
  exact (laws.compose_bound (dataLaws.unit _) (le_refl (sizes.localSize (primitive .zero)))).trans (by omega)

theorem pairZeroCode_description (input : Ty CryptoAtom) :
    sizes.localSize (pairZeroCode rep data cost primitive input) ≤ 2 * sizes.localSize (primitive .zero) + 5 * allowance := by
  have h := zeroCode_description rep data cost primitive sizes allowance laws dataLaws input
  exact (laws.pair_bound h h).trans (by omega)

variable [SampleableType F] (sampling : MachineCompiler.SamplingImplementation Q iface rep) (index : Index)

theorem goodRead_description :
    (goodRead rep data cost primitive sampling index).descriptionSize sizes ≤
      sampling.scalar.descriptionSize sizes + sizes.localSize (primitive .keyEq) +
        2 * sizes.localSize (primitive (.finVal index.bound)) + sizes.localSize (primitive .natEq) +
        sizes.localSize (primitive .zero) + 332 * allowance + 34 := by
  have hc := CacheRead.description rep data (index.code rep data cost primitive)
    (zeroCode rep data cost primitive (inputTy index.ty scalar)) sampling.scalar sizes allowance laws dataLaws
  have hi := index.description rep data cost primitive sizes allowance laws dataLaws
    (fun instr => sizes.localSize (primitive instr)) (fun _ => le_rfl)
  have hz := zeroCode_description rep data cost primitive sizes allowance laws dataLaws (inputTy index.ty scalar)
  exact hc.trans (by omega)

theorem badRead_description :
    (badRead rep data cost primitive sampling index).descriptionSize sizes ≤
      2 * sampling.scalar.descriptionSize sizes + sizes.localSize (primitive .keyEq) +
        2 * sizes.localSize (primitive (.finVal index.bound)) + sizes.localSize (primitive .natEq) +
        2 * sizes.localSize (primitive .zero) + 341 * allowance + 40 := by
  have hc := CacheRead.description rep data (index.code rep data cost primitive)
    (pairZeroCode rep data cost primitive (inputTy index.ty (.pair scalar scalar)))
    (PrivateCache.pairSampler rep data sampling) sizes allowance laws dataLaws
  have hi := index.description rep data cost primitive sizes allowance laws dataLaws
    (fun instr => sizes.localSize (primitive instr)) (fun _ => le_rfl)
  have hz := pairZeroCode_description rep data cost primitive sizes allowance laws dataLaws
    (inputTy index.ty (.pair scalar scalar))
  have hs := PairSampling.description rep.data data (rep.ty scalar) (rep.ty scalar)
    sampling.scalar sampling.scalar sizes allowance laws dataLaws
  change (PrivateCache.pairSampler rep data sampling).descriptionSize sizes ≤ _ at hs
  exact hc.trans (by omega)

end Signatures.Runtime.WeightedAGM.Read
