import Signatures.Runtime.BackendSignatureCallerOutput
import Signatures.Runtime.BackendLazyAGMOutputSize

/-! Recover AGM output and coefficient bounds from actual native caller runs.
For the shared tuple encoding, the attacker's measured head-size bound controls
the entire returned representation, including coefficients beyond the transcript.
The positive-cell list law is explicit; no coefficient-length bound is assumed. -/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.LazyAGM

open BackendProgram Coron

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum] [QO : Q.HasOption]
  [QD : Q.IsDistributive] [OC : OptionCode (Q := Q)]
  {F G₁ G₂ M Input S : Type} [Zero G₁] [DecidableEq M] {randomBound : Nat}
  {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ M M))
  (bd : Boundary C (generalSpec M G₁ randomBound).toPFunctor Input
    ((AGM.outputTy message).Value (cryptoBase F G₁ G₂ M M)))
  (ports : NativePorts (Q := Q) rep bd) (sampler : BoundedSampler rep bd ports (iface := iface))
  (store : C.Str S)
  (reply : (signing : Bool) → Code Q unifSpec iface
    (StepClass.HasProd.prod (rep.ty message) store) (StepClass.HasProd.prod (rep.ty point₁) store))
  (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
  (R : GeneralCaller.Caller (Q := Q) (bd := bd))
  (bound : ExecutionCost) (hrun : R.RunsWithin (fun _ => bound))
  {header : Nat} (sizes : SizeLaws Q header) (lengths : ListLengthLaws Q rep.data)

include hrun sizes lengths

theorem caller_output_bounds_of_resources
    (houtEncoding : bd.out = rep.ty (AGM.outputTy message))
    (fuel : Nat) (input : Input) (saved : S)
    (z : Run (Option ((AGM.outputTy message).Value (cryptoBase F G₁ G₂ M M)) × S))
    (hz : z ∈ support ((SignatureHandler.caller rep bd ports sampler store reply R fuel).run
      control queryCost (input, saved)))
    (out : (AGM.outputTy message).Value (cryptoBase F G₁ G₂ M M)) (hout : z.value.1 = some out) :
    Q.size (rep.ty (AGM.outputTy message)) out ≤ bound.peakHeadSize ∧
      Q.size (rep.ty message) out.1 ≤ bound.peakHeadSize ∧
      (AGM.outputView out).γ.length ≤ bound.peakHeadSize ∧
      (AGM.outputView out).ξ.length ≤ bound.peakHeadSize ∧
      (AGM.outputView out).γ.length + (AGM.outputView out).ξ.length ≤ 2 * bound.peakHeadSize := by
  have ho := SignatureHandler.caller_output_size_of_resources rep bd ports sampler store reply control queryCost
    R bound hrun sizes fuel input saved z hz out hout
  rw [houtEncoding] at ho
  have hm := sizes.fst_le (rep.ty message)
    (rep.ty (.pair scalar (.pair (.list scalar) (.list scalar)))) out
  exact ⟨ho, hm.trans ho, coefficient_lengths_of_output_cap rep sizes lengths out bound.peakHeadSize ho⟩

end Signatures.Runtime.LazyAGM
