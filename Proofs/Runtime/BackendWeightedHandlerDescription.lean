import Proofs.Runtime.BackendWeightedHandler
import Proofs.Runtime.BackendCallerDescription
import Proofs.Runtime.BackendLanguageSize

/-! Stored-description bounds for shared native signature dispatch. Both group
branches, request conversion, reply tags, and one dynamic random sampler are
counted. There is no code table indexed by messages or randomness arities. -/

open OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.WeightedAGM.NativeHandler

open BackendProgram

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum] [QD : Q.IsDistributive]
  {iface : Interface (C := C) unifSpec}
  {S : Type} (store : C.Str S)
  (sizes : DescriptionSize Q) (allowance : Nat) (laws : LocalDescriptionLaws sizes allowance)

include laws

section Group

variable {R G I : Type} (request : C.Str R) (point : C.Str G) (index : C.Str I)
  {tag : R × G → I} (tagCode : Q.Realizer (StepClass.HasProd.prod request point) index tag)
  (reply : Code Q unifSpec iface
    (StepClass.HasProd.prod request store) (StepClass.HasProd.prod point store))

omit QD in
theorem group_description :
    (group request point index store tagCode reply).descriptionSize sizes ≤
      reply.descriptionSize sizes + sizes.localSize tagCode + 18 * allowance + 8 := by
  have hc := Language.withContext_descriptionSize sizes allowance laws store (Q.identity request) reply
  have hi := laws.identity request
  have ht : sizes.localSize (Q.compose
      (QP.pair (QP.snd point request) (QP.fst point request)) tagCode) ≤
      sizes.localSize tagCode + 4 * allowance :=
    (laws.compose_bound (laws.pair_bound (laws.snd _ _) (laws.fst _ _))
      (le_refl (sizes.localSize tagCode))).trans (by omega)
  dsimp only [group, Code.descriptionSize]
  omega

end Group

variable {F G₁ G₂ K M Input Output : Type} {randomBound : Nat}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (indexTy messageTy : Ty CryptoAtom)
  (bd : Boundary C (generalSpec (indexTy.Value (cryptoBase F G₁ G₂ K M))
    (messageTy.Value (cryptoBase F G₁ G₂ K M)) G₁ randomBound).toPFunctor Input Output)
  (ports : NativePorts (Q := Q) rep indexTy messageTy bd)
  (sampler : BoundedSampler rep indexTy messageTy bd ports (iface := iface))
  (hashReply : Code Q unifSpec iface
    (StepClass.HasProd.prod (rep.ty indexTy) store) (StepClass.HasProd.prod (rep.ty point₁) store))
  (signReply : Code Q unifSpec iface
    (StepClass.HasProd.prod (rep.ty messageTy) store) (StepClass.HasProd.prod (rep.ty point₁) store))

omit laws [Q.HasCategory] QP QS QD in
theorem random_description :
    (random rep indexTy messageTy bd ports sampler store).descriptionSize sizes =
      sampler.code.descriptionSize sizes + sizes.localSize ports.randomTag + 4 := by
  dsimp only [random, Code.descriptionSize]
  omega

variable [C.HasOption] [QO : Q.HasOption] [OC : OptionCode (Q := Q)]
  (dispatchLaws : DispatchDescriptionLaws (Q := Q) sizes allowance)

include dispatchLaws

theorem code_description :
    (code rep indexTy messageTy bd ports sampler store hashReply signReply).descriptionSize sizes ≤
      hashReply.descriptionSize sizes + signReply.descriptionSize sizes +
      sampler.code.descriptionSize sizes + sizes.localSize ports.request +
      sizes.localSize ports.randomTag + sizes.localSize ports.hashTag +
      sizes.localSize ports.signTag + 40 * allowance + 32 := by
  have hh := group_description store sizes allowance laws (rep.ty indexTy) (rep.ty point₁) bd.idx ports.hashTag hashReply
  have hs := group_description store sizes allowance laws (rep.ty messageTy) (rep.ty point₁) bd.idx ports.signTag signReply
  have hr := random_description store sizes rep indexTy messageTy bd ports sampler
  have hd1 := dispatchLaws.distribute (rep.ty (boundedNat randomBound)) (rep.ty indexTy) store
  have hd2 := dispatchLaws.distribute (StepClass.HasSum.sum (rep.ty (boundedNat randomBound)) (rep.ty indexTy))
    (rep.ty messageTy) store
  dsimp only [code, dispatch, inner, Code.descriptionSize, generalPositions] at *
  omega

variable [DecidableEq (indexTy.Value (cryptoBase F G₁ G₂ K M))]
  [DecidableEq (messageTy.Value (cryptoBase F G₁ G₂ K M))] (R : GeneralCaller.Caller (Q := Q) (bd := bd))

/-- Caller code is stored once, with one copy of the dispatcher and explicit
loop-fuel/structural overhead. It does not expand into a table of oracle replies. -/
theorem caller_description (fuel : Nat) :
    (caller rep indexTy messageTy bd ports sampler store hashReply signReply R fuel).descriptionSize sizes ≤
      sizes.localSize R.initCode + 2 * sizes.localSize R.headCode + sizes.localSize R.updateCode +
      (code rep indexTy messageTy bd ports sampler store hashReply signReply).descriptionSize sizes + fuel + 55 * allowance + 26 :=
  Caller.program_descriptionSize_bound R store sizes allowance laws dispatchLaws
    (code rep indexTy messageTy bd ports sampler store hashReply signReply) fuel

end Signatures.Runtime.WeightedAGM.NativeHandler
