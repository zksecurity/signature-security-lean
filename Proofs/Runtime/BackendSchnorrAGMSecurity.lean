import Proofs.Runtime.BackendSchnorrAGMDLog
import Proofs.Runtime.SchnorrAGMSecurity

/-! Concrete Schnorr AGM security from a general realized caller in one fixed
backend. The entire DLog solver's resource witness is derived before applying
hardness. The source game's original query losses and arbitrary messages remain. -/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation
open scoped ENNReal

namespace Signatures.Runtime.SchnorrAGM.Native.Solver

open BackendProgram Interface

universe v w x

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum] [Q.HasOption]
  [QD : Q.IsDistributive] [OptionCode (Q := Q)]
  {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  [DecidableEq (SourceRequest F G₁ M)]
  {iface : BackendProgram.Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (bd : Boundary C (sourceSpec F G₁ M).toPFunctor (SourceInput G₁) (SourceForgery F G₁ M))
  (boundary : DataPorts (Q := Q) rep bd)
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  (ports : Ports (Q := Q) rep bd)
  (randomPorts : UniformSampling.Ports (Q := Q) rep.data (iface := iface))
  (sampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))
  (R : GeneralCaller.Caller (Q := Q) (bd := bd))
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)
  (lengths : ListLengthLaws Q rep.data) (payloads : ListPayloadLaws Q rep.data)
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
  (mono : Monotone overhead)
  (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
  (routing : RoutingCostLaws control overhead) (dispatch : DispatchCostLaws (Q := Q) overhead)
  (recovery : Handler.RequestRecovery (Q := Q) rep bd)
  (bound : ExecutionCost) (hrun : R.RunsWithin (fun _ => bound))

include sizes lists lengths payloads laws dataLaws primitiveBound mono routing dispatch recovery hrun

variable [SampleableType F] [Fintype F]
  (backend : Backend.{v, w, x} Q unifSpec iface control queryCost)
  (descriptionSizes : DescriptionSize Q) (factor : Nat)
  (description : backend.DescriptionBound descriptionSizes factor)
  (allowance : Nat) (descriptionLaws : LocalDescriptionLaws descriptionSizes allowance)
  (descriptionData : DataDescriptionLaws descriptionSizes rep.data data allowance)
  (descriptionDispatch : DispatchDescriptionLaws (Q := Q) descriptionSizes allowance)

include descriptionLaws descriptionData descriptionDispatch

theorem security_of_resources
    (inputWidth width outputWidth routeWidth cap basisCap signedCap groupCap rowCap coeffCap arityCap portWidth
      fuel tickTime adapterTime divisionTime : Nat) (t : Handler.Times)
    (hh : header ≤ width) (hc : fuel ≤ cap) (hn : fuel + 2 ≤ basisCap) (hs : fuel ≤ signedCap)
    (hroute : Handler.frameWidth width cap basisCap signedCap groupCap rowCap coeffCap portWidth ≤ routeWidth)
    (handlerCaps : Handler.PortCaps rep bd ports width groupCap rowCap coeffCap arityCap portWidth t.requestTime t.tagTime)
    (solverCaps : PortCaps rep bd boundary width outputWidth routeWidth adapterTime)
    (primitives : Handler.PrimitiveCaps rep cost primitive randomPorts sampler control queryCost primitiveBound width basisCap arityCap t)
    (hrequest : recovery.recover bound.peakHeadSize ≤ width)
    (hgroups : recovery.recover bound.peakHeadSize ≤ groupCap)
    (hrows : recovery.recover bound.peakHeadSize ≤ rowCap)
    (hcoeff : recovery.recover bound.peakHeadSize ≤ coeffCap)
    (harity : recovery.natural.capacity (recovery.recover bound.peakHeadSize) ≤ arityCap)
    (hstate : bound.peakStateSize ≤ routeWidth) (hhead : bound.peakHeadSize ≤ routeWidth)
    (htick : ∀ n ≤ fuel, ∀ encoded ≤ 3 * routeWidth, control.loop n encoded ≤ tickTime)
    (hone : (primitiveBound .one).time () ≤ t.fieldTime)
    (hm : ∀ a b : M, Q.size (rep.ty message) a ≤ 15 * max width outputWidth →
      Q.size (rep.ty message) b ≤ 15 * max width outputWidth → (primitiveBound .messageEq).time (a, b) ≤ t.messageTime)
    (hg : ∀ a b : G₁, Q.size (rep.ty point₁) a ≤ 15 * max width outputWidth →
      Q.size (rep.ty point₁) b ≤ 15 * max width outputWidth → (primitiveBound .point₁Eq).time (a, b) ≤ t.pointTime)
    (hsub : ∀ a b : F, (primitiveBound .sub).time (a, b) ≤ t.fieldTime)
    (hdiv : ∀ a b : F, (primitiveBound .div).time (a, b) ≤ divisionTime)
    (hsample : sampler.denote () = ($ᵗ F : ProbComp F))
    (hfuel : bound.queries ≤ fuel)
    (adv : Schnorr.AGM.Adversary F G₁ M) (hprogram : R.machine.Implements adv.main)
    (instructionSize randomPortSize handlerPortSize solverPortSize : Nat)
    (hinstr : ∀ {a b} (instr : CryptoOp a b), descriptionSizes.localSize (primitive instr) ≤ instructionSize)
    (hrandomRequest : descriptionSizes.localSize randomPorts.request ≤ randomPortSize)
    (hrandomResponse : descriptionSizes.localSize randomPorts.response ≤ randomPortSize)
    (hhandler : descriptionSizes.localSize ports.request ≤ handlerPortSize ∧ descriptionSizes.localSize ports.randomTag ≤ handlerPortSize ∧
      descriptionSizes.localSize (ports.scalarTag false) ≤ handlerPortSize ∧ descriptionSizes.localSize (ports.scalarTag true) ≤ handlerPortSize)
    (hsolver : descriptionSizes.localSize boundary.input ≤ solverPortSize ∧ descriptionSizes.localSize boundary.output ≤ solverPortSize ∧
      descriptionSizes.localSize boundary.optional ≤ solverPortSize)
    (g : G₁) (hgen : Function.Injective (fun x : F => x • g))
    (qS qH : Nat)
    (hS : ∀ pk, IsQueryBoundP (adv.main (Schnorr.AGM.initial g pk))
      (fun q => Schnorr.AGM.Reduction.signRequest q = true) qS)
    (hH : ∀ pk, IsQueryBoundP (adv.main (Schnorr.AGM.initial g pk))
      (fun q => Schnorr.AGM.Reduction.hashRequest q = true) qH)
    (hchallenge : ∀ x : F, Q.size (rep.env inputTypes) (g, x • g, ()) ≤ inputWidth)
    (codeBudget timeBudget : Nat) (epsilon : ENNReal)
    (hcode : factor * programDescription
        (descriptionSizes.localSize R.initCode + 2 * descriptionSizes.localSize R.headCode + descriptionSizes.localSize R.updateCode)
        (sampler.descriptionSize descriptionSizes) randomPortSize handlerPortSize solverPortSize fuel allowance instructionSize ≤ codeBudget)
    (htime : programTime overhead bound inputWidth width outputWidth routeWidth cap basisCap signedCap
        groupCap rowCap coeffCap portWidth fuel tickTime adapterTime divisionTime t ≤ timeBudget)
    (hardness : Model.HardWithin (fun solver => 𝒟[DiffieHellman.dlogExperiment g solver] {true})
      (dlogWithin rep backend descriptionSizes factor description g inputWidth codeBudget) timeBudget epsilon) :
    𝒟[Schnorr.AGM.game g adv] {true} ≤ epsilon +
      (qH + 1 : ENNReal) * (Fintype.card F : ENNReal)⁻¹ +
      (qS : ENNReal) * (qS + qH) * (Fintype.card F : ENNReal)⁻¹ := by
  have certificate := program_within rep bd boundary data cost primitive ports randomPorts sampler R
    sizes lists lengths payloads laws dataLaws primitiveBound mono control queryCost routing dispatch recovery bound hrun
    backend descriptionSizes factor description allowance descriptionLaws descriptionData descriptionDispatch
    inputWidth width outputWidth routeWidth cap basisCap signedCap groupCap rowCap coeffCap arityCap portWidth
    fuel tickTime adapterTime divisionTime t hh hc hn hs hroute handlerCaps solverCaps primitives
    hrequest hgroups hrows hcoeff harity hstate hhead htick hone hm hg hsub hdiv
    hsample hfuel adv hprogram instructionSize randomPortSize handlerPortSize solverPortSize
    hinstr hrandomRequest hrandomResponse hhandler hsolver
  have hdlog := hardness (dlogReduction adv)
    ⟨hchallenge, Within.mono backend descriptionSizes factor description certificate hcode htime⟩
  exact (SchnorrAGM.security g hgen adv qS qH hS hH).trans
    (add_le_add (add_le_add hdlog le_rfl) le_rfl)

end Signatures.Runtime.SchnorrAGM.Native.Solver
