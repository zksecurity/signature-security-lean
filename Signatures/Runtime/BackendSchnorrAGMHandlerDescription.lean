import Signatures.Runtime.BackendSchnorrAGMHandlerSource
import Signatures.Runtime.BackendCallerDescription

/-! Stored-code accounting for the installed Schnorr dispatcher and general
caller. Every component, request conversion, reply tag and routing adapter is
included; no code table is indexed by messages, group values or random arities. -/

open OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.SchnorrAGM.Native.Handler

open BackendProgram Interface

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {F G₁ G₂ K M Input Output : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  {iface : BackendProgram.Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (bd : Boundary C (sourceSpec F G₁ M).toPFunctor Input Output)
  (ports : Ports (Q := Q) rep bd)
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  (randomPorts : UniformSampling.Ports (Q := Q) rep.data (iface := iface))
  (sampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))
  (sizes : DescriptionSize Q) (allowance : Nat) (laws : LocalDescriptionLaws sizes allowance)
  (dataLaws : DataDescriptionLaws sizes rep.data data allowance)

include laws dataLaws

private theorem components_description :
    (HandlerComponents.random rep data cost primitive randomPorts).descriptionSize sizes ≤
      (Random.code rep data cost primitive randomPorts).descriptionSize sizes + 1024 * allowance + 8 ∧
    (HandlerComponents.hash rep data cost primitive sampler).descriptionSize sizes ≤
      (HashDispatch.code rep data cost primitive sampler).descriptionSize sizes + 1024 * allowance + 8 ∧
    (HandlerComponents.signing rep data cost primitive sampler).descriptionSize sizes ≤
      (SigningDispatch.code rep data cost primitive sampler).descriptionSize sizes + 1024 * allowance + 8 := by
  have hlocal {a b : Ty CryptoAtom} (e : Expr CryptoOp [a] b) :=
    HandlerComponents.localCode_description rep data cost primitive e sizes allowance laws dataLaws
      (fun instr => sizes.localSize (primitive instr)) (fun _ => le_rfl)
  have hr : sizes.localSize (HandlerComponents.localCode rep data cost primitive HandlerComponents.randomInputExpression) ≤ 512 * allowance := by
    refine (hlocal _).trans ?_
    simp only [HandlerComponents.randomInputExpression, Expression.descriptionBound, Expression.variableDescription]
    omega
  have hh : sizes.localSize (HandlerComponents.localCode rep data cost primitive HandlerComponents.hashInputExpression) ≤ 512 * allowance := by
    refine (hlocal _).trans ?_
    simp only [HandlerComponents.hashInputExpression, Expression.descriptionBound, Expression.variableDescription]
    omega
  have hs : sizes.localSize (HandlerComponents.localCode rep data cost primitive HandlerComponents.signingInputExpression) ≤ 512 * allowance := by
    refine (hlocal _).trans ?_
    simp only [HandlerComponents.signingInputExpression, Expression.descriptionBound, Expression.variableDescription]
    omega
  have hg (value : Ty CryptoAtom) : sizes.localSize (HandlerComponents.localCode rep data cost primitive
      (HandlerComponents.groupOutputExpression value)) ≤ 128 * allowance := by
    refine (hlocal _).trans ?_
    simp only [HandlerComponents.groupOutputExpression, Expression.descriptionBound, Expression.variableDescription]
    omega
  have hhash : sizes.localSize (HandlerComponents.localCode rep data cost primitive HandlerComponents.hashOutputExpression) ≤ 128 * allowance := by
    refine (hlocal _).trans ?_
    simp only [HandlerComponents.hashOutputExpression, Expression.descriptionBound, Expression.variableDescription]
    omega
  have hnat := hg .nat
  have hfield := hg scalar
  dsimp only [HandlerComponents.random, HandlerComponents.hash, HandlerComponents.signing, Code.descriptionSize]
  omega

omit dataLaws in
theorem random_description :
    (random rep bd ports data cost primitive randomPorts).descriptionSize sizes ≤
      (HandlerComponents.random rep data cost primitive randomPorts).descriptionSize sizes +
        sizes.localSize ports.randomTag + 18 * allowance + 8 := by
  have hc := Language.withContext_descriptionSize sizes allowance laws (rep.ty storeTy)
    (Q.identity (rep.ty randomArgsTy)) (HandlerComponents.random rep data cost primitive randomPorts)
  have hi := laws.identity (rep.ty randomArgsTy)
  have ht : sizes.localSize (Q.compose
      (QP.pair (QP.snd (rep.ty (groupReplyTy .nat)) (rep.ty randomArgsTy))
        (QP.fst (rep.ty (groupReplyTy .nat)) (rep.ty randomArgsTy))) ports.randomTag) ≤
      sizes.localSize ports.randomTag + 4 * allowance :=
    (laws.compose_bound (laws.pair_bound (laws.snd _ _) (laws.fst _ _)) (le_refl _)).trans (by omega)
  dsimp only [random, Code.descriptionSize]
  omega

omit dataLaws in
theorem group_description (signing : Bool) :
    (group rep bd ports data cost primitive sampler signing).descriptionSize sizes ≤
      (groupCode rep data cost primitive sampler signing).descriptionSize sizes +
        sizes.localSize (ports.scalarTag signing) + 18 * allowance + 8 := by
  have hc := Language.withContext_descriptionSize sizes allowance laws (rep.ty storeTy)
    (Q.identity (rep.ty groupArgsTy)) (groupCode rep data cost primitive sampler signing)
  have hi := laws.identity (rep.ty groupArgsTy)
  have ht : sizes.localSize (Q.compose
      (QP.pair (QP.snd (rep.ty scalarGroupReplyTy) (rep.ty groupArgsTy))
        (QP.fst (rep.ty scalarGroupReplyTy) (rep.ty groupArgsTy))) (ports.scalarTag signing)) ≤
      sizes.localSize (ports.scalarTag signing) + 4 * allowance :=
    (laws.compose_bound (laws.pair_bound (laws.snd _ _) (laws.fst _ _)) (le_refl _)).trans (by omega)
  dsimp only [group, Code.descriptionSize]
  omega

variable [C.HasOption] [QO : Q.HasOption] [OC : OptionCode (Q := Q)] [QD : Q.IsDistributive]
  (dispatchLaws : DispatchDescriptionLaws (Q := Q) sizes allowance)

include dispatchLaws

theorem code_description (primitiveSize : {a b : Ty CryptoAtom} → CryptoOp a b → Nat)
    (hp : ∀ {a b} (instr : CryptoOp a b), sizes.localSize (primitive instr) ≤ primitiveSize instr) :
    (code rep bd ports data cost primitive randomPorts sampler).descriptionSize sizes ≤
      3 * sampler.descriptionSize sizes + sizes.localSize randomPorts.request + sizes.localSize randomPorts.response +
        sizes.localSize ports.request + sizes.localSize ports.randomTag +
        sizes.localSize (ports.scalarTag false) + sizes.localSize (ports.scalarTag true) +
        2 * primitiveSize .messageEq + 2 * primitiveSize .point₁Eq + 3 * primitiveSize .add +
        6 * primitiveSize .zero + primitiveSize .zero₁ + primitiveSize .scalarEq +
        primitiveSize .natEq + primitiveSize .natSub + primitiveSize .natAdd + 2 * primitiveSize .mul +
        primitiveSize .neg + 2 * primitiveSize .scale₁ + primitiveSize .sub₁ + 14000 * allowance + 256 := by
  have hcomponents := components_description rep data cost primitive randomPorts sampler sizes allowance laws dataLaws
  have hr := random_description rep bd ports data cost primitive randomPorts sizes allowance laws
  have hh := group_description rep bd ports data cost primitive sampler sizes allowance laws false
  have hs := group_description rep bd ports data cost primitive sampler sizes allowance laws true
  have hrandom := Random.description rep data cost primitive randomPorts sizes allowance laws dataLaws
  have hhash := HashDispatch.description rep data cost primitive sampler sizes allowance laws dataLaws primitiveSize hp
  have hsign := SigningDispatch.description rep data cost primitive sampler sizes allowance laws dataLaws primitiveSize hp
  have hd₁ := dispatchLaws.distribute (rep.ty groupArgsTy) (rep.ty groupArgsTy) (rep.ty storeTy)
  have hd₂ := dispatchLaws.distribute (rep.ty randomArgsTy)
    (StepClass.HasSum.sum (rep.ty groupArgsTy) (rep.ty groupArgsTy)) (rep.ty storeTy)
  simp only [groupCode, Bool.false_eq_true, ↓reduceIte] at hh hs
  dsimp only [code, dispatch, inner, Code.descriptionSize, positions]
  omega

variable [DecidableEq (SourceRequest F G₁ M)] (R : GeneralCaller.Caller (Q := Q) (bd := bd))

omit dataLaws in
theorem caller_description (fuel : Nat) :
    (caller rep bd ports data cost primitive randomPorts sampler R fuel).descriptionSize sizes ≤
      sizes.localSize R.initCode + 2 * sizes.localSize R.headCode + sizes.localSize R.updateCode +
        (code rep bd ports data cost primitive randomPorts sampler).descriptionSize sizes + fuel + 55 * allowance + 26 :=
  Caller.program_descriptionSize_bound R (rep.ty storeTy) sizes allowance laws dispatchLaws
    (code rep bd ports data cost primitive randomPorts sampler) fuel

end Signatures.Runtime.SchnorrAGM.Native.Handler
