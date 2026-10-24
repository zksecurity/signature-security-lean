import Proofs.Runtime.BackendSignatureHandler
import Proofs.Runtime.BackendCallerDescription

/-! Stored-description bounds for shared native signature dispatch. Both group
branches, request conversion, reply tags, and one dynamic random sampler are
counted. There is no code table indexed by messages or randomness arities. -/

open OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.SignatureHandler

open BackendProgram Coron

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum] [QD : Q.IsDistributive]
  {F G₁ G₂ M Input Output S : Type} {randomBound : Nat}
  {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ M M))
  (bd : Boundary C (generalSpec M G₁ randomBound).toPFunctor Input Output)
  (ports : NativePorts (Q := Q) rep bd) (sampler : BoundedSampler rep bd ports (iface := iface))
  (store : C.Str S)
  (reply : (signing : Bool) → Code Q unifSpec iface
    (StepClass.HasProd.prod (rep.ty message) store) (StepClass.HasProd.prod (rep.ty point₁) store))
  (sizes : DescriptionSize Q) (allowance : Nat) (laws : LocalDescriptionLaws sizes allowance)

include laws

omit QD in
theorem group_description (signing : Bool) :
    (group rep bd ports store reply signing).descriptionSize sizes ≤
      (reply signing).descriptionSize sizes + sizes.localSize (ports.groupTag signing) + 18 * allowance + 8 := by
  have hc := Language.withContext_descriptionSize sizes allowance laws store (Q.identity (rep.ty message)) (reply signing)
  have hi := laws.identity (rep.ty message)
  have ht : sizes.localSize (Q.compose
      (QP.pair (QP.snd (rep.ty point₁) (rep.ty message)) (QP.fst (rep.ty point₁) (rep.ty message)))
      (ports.groupTag signing)) ≤ sizes.localSize (ports.groupTag signing) + 4 * allowance :=
    (laws.compose_bound (laws.pair_bound (laws.snd _ _) (laws.fst _ _))
      (le_refl (sizes.localSize (ports.groupTag signing)))).trans (by omega)
  dsimp only [group, Code.descriptionSize]
  omega

omit laws [Q.HasCategory] QP QS QD in
theorem random_description :
    (random rep bd ports sampler store).descriptionSize sizes =
      sampler.code.descriptionSize sizes + sizes.localSize ports.randomTag + 4 := by
  dsimp only [random, Code.descriptionSize]
  omega

variable [C.HasOption] [QO : Q.HasOption] [OC : OptionCode (Q := Q)]
  (dispatchLaws : DispatchDescriptionLaws (Q := Q) sizes allowance)

include dispatchLaws

theorem code_description :
    (code rep bd ports sampler store reply).descriptionSize sizes ≤
      (reply false).descriptionSize sizes + (reply true).descriptionSize sizes +
      sampler.code.descriptionSize sizes + sizes.localSize ports.request +
      sizes.localSize ports.randomTag + sizes.localSize (ports.groupTag false) +
      sizes.localSize (ports.groupTag true) + 40 * allowance + 32 := by
  have hh := group_description rep bd ports store reply sizes allowance laws false
  have hs := group_description rep bd ports store reply sizes allowance laws true
  have hr := random_description rep bd ports sampler store sizes
  have hd1 := dispatchLaws.distribute (rep.ty (boundedNat randomBound)) (rep.ty message) store
  have hd2 := dispatchLaws.distribute (StepClass.HasSum.sum (rep.ty (boundedNat randomBound)) (rep.ty message))
    (rep.ty message) store
  dsimp only [code, dispatch, inner, Code.descriptionSize, generalPositions] at *
  omega

variable [DecidableEq M] (R : GeneralCaller.Caller (Q := Q) (bd := bd))

/-- Caller code is stored once, with one copy of the dispatcher and explicit
loop-fuel/structural overhead. It does not expand into a table of oracle replies. -/
theorem caller_description (fuel : Nat) :
    (caller rep bd ports sampler store reply R fuel).descriptionSize sizes ≤
      sizes.localSize R.initCode + 2 * sizes.localSize R.headCode + sizes.localSize R.updateCode +
      (code rep bd ports sampler store reply).descriptionSize sizes + fuel + 55 * allowance + 26 :=
  Caller.program_descriptionSize_bound R store sizes allowance laws dispatchLaws
    (code rep bd ports sampler store reply) fuel

end Signatures.Runtime.SignatureHandler
