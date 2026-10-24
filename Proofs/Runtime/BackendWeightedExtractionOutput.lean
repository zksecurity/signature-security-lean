import Proofs.Runtime.BackendWeightedCallerOutput
import Proofs.Runtime.BackendWeightedOutputSize

/-! Recover AGM output and coefficient bounds from actual native caller runs.
For the shared tuple encoding, the attacker's measured head-size bound controls
the entire returned representation, including coefficients beyond the transcript.
The positive-cell list law is explicit; no coefficient-length bound is assumed. -/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.WeightedAGM

open BackendProgram

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum] [QO : Q.HasOption]
  [QD : Q.IsDistributive] [OC : OptionCode (Q := Q)]
  {F G₁ G₂ K M Input S : Type} [Zero G₁] {randomBound : Nat}
  {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (indexTy messageTy : Ty CryptoAtom)
  [DecidableEq (indexTy.Value (cryptoBase F G₁ G₂ K M))]
  [DecidableEq (messageTy.Value (cryptoBase F G₁ G₂ K M))]
  (bd : Boundary C (generalSpec (indexTy.Value (cryptoBase F G₁ G₂ K M)) (messageTy.Value (cryptoBase F G₁ G₂ K M)) G₁ randomBound).toPFunctor Input
    ((AGM.outputTy messageTy).Value (cryptoBase F G₁ G₂ K M)))
  (ports : NativePorts (Q := Q) rep indexTy messageTy bd) (sampler : BoundedSampler rep indexTy messageTy bd ports (iface := iface))
  (store : C.Str S)
  (hashReply : Code Q unifSpec iface
    (StepClass.HasProd.prod (rep.ty indexTy) store) (StepClass.HasProd.prod (rep.ty point₁) store))
  (signReply : Code Q unifSpec iface
    (StepClass.HasProd.prod (rep.ty messageTy) store) (StepClass.HasProd.prod (rep.ty point₁) store))
  (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
  (R : GeneralCaller.Caller (Q := Q) (bd := bd))
  (bound : ExecutionCost) (hrun : R.RunsWithin (fun _ => bound))
  {header : Nat} (sizes : SizeLaws Q header) (lengths : ListLengthLaws Q rep.data)

include hrun sizes lengths

theorem caller_output_bounds_of_resources
    (houtEncoding : bd.out = rep.ty (AGM.outputTy messageTy))
    (fuel : Nat) (input : Input) (saved : S)
    (z : Run (Option ((AGM.outputTy messageTy).Value (cryptoBase F G₁ G₂ K M)) × S))
    (hz : z ∈ support ((NativeHandler.caller rep indexTy messageTy bd ports sampler store hashReply signReply R fuel).run
      control queryCost (input, saved)))
    (out : (AGM.outputTy messageTy).Value (cryptoBase F G₁ G₂ K M)) (hout : z.value.1 = some out) :
    Q.size (rep.ty (AGM.outputTy messageTy)) out ≤ bound.peakHeadSize ∧
      Q.size (rep.ty messageTy) out.1 ≤ bound.peakHeadSize ∧
      (AGM.outputView out).γ.length ≤ bound.peakHeadSize ∧
      (AGM.outputView out).ξ.length ≤ bound.peakHeadSize ∧
      (AGM.outputView out).γ.length + (AGM.outputView out).ξ.length ≤ 2 * bound.peakHeadSize := by
  have ho := NativeHandler.caller_output_size_of_resources rep indexTy messageTy bd ports sampler store hashReply signReply control queryCost
    R bound hrun sizes fuel input saved z hz out hout
  rw [houtEncoding] at ho
  have hm := sizes.fst_le (rep.ty messageTy)
    (rep.ty (.pair scalar (.pair (.list scalar) (.list scalar)))) out
  exact ⟨ho, hm.trans ho, coefficient_lengths_of_output_cap rep sizes lengths out bound.peakHeadSize ho⟩

end Signatures.Runtime.WeightedAGM
