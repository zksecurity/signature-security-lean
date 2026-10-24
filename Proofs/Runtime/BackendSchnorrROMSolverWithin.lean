import Proofs.Runtime.BackendSchnorrROMSolverBudget
import Proofs.Runtime.BackendSchnorrROMDescriptionInputs
import Proofs.Runtime.BackendSchnorrROMReduction
import Proofs.Runtime.BackendWithin

/-! An executable witness in the common fixed backend for the complete general
Schnorr ROM reduction. Runtime, full stored code and source semantics follow
from original resource and representation contracts, not a supplied solver budget. -/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.Schnorr.ListROM.NativeSolver

open BackendProgram RawTape NativeInterface NativeComponents

universe v w x

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {F G₁ G₂ K M : Type}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))

variable {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)

variable [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum] [Q.IsDistributive]
  [Q.HasOption] [OptionCode (Q := Q)]
  [Field F] [SampleableType F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  {iface : Interface (C := C) unifSpec}
  (bd : Boundary C (sourceSpec F G₁ M).toPFunctor G₁ (M × G₁ × F))
  (boundary : NativePass.DataPorts (Q := Q) rep bd) (ports : Ports (Q := Q) rep bd)
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  (uniform : UniformSampling.Ports (Q := Q) rep.data (iface := iface))
  (privatePorts : NativePrivate.Ports (Q := Q) rep (iface := iface))
  (sampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))
  (sample : sampler.denote () = ($ᵗ F : ProbComp F))
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
  (mono : Monotone overhead)
  (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
  (routing : RoutingCostLaws control overhead) (dispatch : DispatchCostLaws (Q := Q) overhead)
  (R : GeneralCaller.Caller (Q := Q) (bd := bd))
  (recovery : NativeHandler.RequestRecovery (Q := Q) rep bd)
  (bound : ExecutionCost) (hrun : R.RunsWithin (fun _ => bound))

variable
  (backend : Backend.{v, w, x} Q unifSpec iface control queryCost)
  (descriptionSizes : DescriptionSize Q) (factor : Nat)
  (description : backend.DescriptionBound descriptionSizes factor)
  (allowance : Nat) (descriptionLaws : LocalDescriptionLaws descriptionSizes allowance)
  (descriptionData : DataDescriptionLaws descriptionSizes rep.data data allowance)
  (descriptionDispatch : DispatchDescriptionLaws (Q := Q) descriptionSizes allowance)

include sample sizes lists laws dataLaws mono routing dispatch hrun
  descriptionLaws descriptionData descriptionDispatch

theorem program_within (inputWidth width tapeWidth managedCap liveCap fuel qH : Nat)
    (first : NativePass.Resources rep bd boundary ports cost primitive uniform privatePorts sampler primitiveBound
      control queryCost recovery bound (header := header) width tapeWidth managedCap liveCap 0 0 fuel)
    (second : NativePass.Resources rep bd boundary ports cost primitive uniform privatePorts sampler primitiveBound
      control queryCost recovery bound (header := header) width tapeWidth managedCap liveCap
        (first.savedCap + 2) (first.savedCap + 2) fuel)
    (scaleTime addTime messageTime pointTime incrementTime comparisonTime scalarComparisonTime subtractTime
      extractionScalarTime fieldSubTime divTime : Nat)
    (selectorOps : NativeSelection.Operations rep cost primitive primitiveBound width (liveCap + 1) qH
      scaleTime addTime messageTime pointTime incrementTime comparisonTime)
    (extractionOps : NativeExtraction.Operations rep cost primitive primitiveBound width pointTime
      extractionScalarTime fieldSubTime divTime first.zeroTime)
    (hn : ∀ n ≤ max (liveCap + 1) qH + 1, Q.size rep.data.nat n ≤ tapeWidth)
    (hscalar : ∀ f g, Q.size (rep.ty scalar) f ≤ tapeWidth → Q.size (rep.ty scalar) g ≤ tapeWidth →
      (primitiveBound .scalarEq).time (f, g) ≤ scalarComparisonTime)
    (hsub : ∀ n ≤ qH, (primitiveBound .natSub).time (n, 1) ≤ subtractTime)
    (hinl : Q.cost (QS.inl rep.data.unit (rep.ty (.pair NativePass.outputTy NativePass.outputTy))) () ≤
      overhead (Q.size rep.data.unit () +
        Q.size (StepClass.HasSum.sum rep.data.unit (rep.ty (.pair NativePass.outputTy NativePass.outputTy))) (.inl ())))
    (hinr : ∀ p, Q.cost (QS.inr rep.data.unit (rep.ty (.pair NativePass.outputTy NativePass.outputTy))) p ≤
      overhead (Q.size (rep.ty (.pair NativePass.outputTy NativePass.outputTy)) p +
        Q.size (StepClass.HasSum.sum rep.data.unit (rep.ty (.pair NativePass.outputTy NativePass.outputTy))) (.inr p)))
    (hinput : inputWidth ≤ width) (hfuel : bound.queries ≤ fuel)
    (attacker : G₁ → OracleComp (sourceSpec F G₁ M) (M × G₁ × F))
    (implementation : R.machine.Implements attacker) :
    Within backend descriptionSizes factor description (rep.env inputTypes) (rep.ty scalar) inputWidth
      (factor * (descriptionInputs rep cost primitive sampler descriptionSizes bd boundary ports uniform privatePorts R).solver
        allowance fuel qH)
      (resourcesTime overhead bound width tapeWidth managedCap liveCap fuel first.timeInputs second.timeInputs
        scaleTime addTime messageTime pointTime incrementTime comparisonTime scalarComparisonTime subtractTime
        extractionScalarTime fieldSubTime divTime)
      (fun input => reduction (G₂ := G₂) (K := K) attacker qH input.1 input.2.1) := by
  have he : ∀ input,
      (code rep bd boundary data cost primitive sampler ports uniform privatePorts R fuel qH).denote input =
        reduction (G₂ := G₂) (K := K) attacker qH input.1 input.2.1 := by
    rintro ⟨g, pk, u⟩
    cases u
    exact source_of_resources rep bd boundary data cost primitive sampler ports uniform privatePorts R sample
      bound hrun fuel qH hfuel attacker implementation g pk
  have hb := code_bound_of_resources rep sizes lists bd boundary ports data cost primitive uniform privatePorts
    sampler sample laws dataLaws primitiveBound mono control queryCost routing dispatch R recovery bound hrun
    width tapeWidth managedCap liveCap fuel qH first second scaleTime addTime messageTime pointTime incrementTime
    comparisonTime scalarComparisonTime subtractTime extractionScalarTime fieldSubTime divTime
    selectorOps extractionOps hn hscalar hsub hinl hinr
  have inputBound (input) (hi : Q.size (rep.env inputTypes) input ≤ inputWidth) : InputBound (Q := Q) rep width input := by
    have hg := sizes.fst_le (rep.ty point₁) (rep.env [point₁]) input
    have ht := sizes.snd_le (rep.ty point₁) (rep.env [point₁]) input
    have hpk := sizes.fst_le (rep.ty point₁) rep.data.unit input.2
    exact ⟨hg.trans (hi.trans hinput), hpk.trans (ht.trans (hi.trans hinput))⟩
  have hb' := Bounds.consequence control queryCost hb inputBound (fun _ _ => True.intro)
  have hw := within_compile backend descriptionSizes factor description
    (code rep bd boundary data cost primitive sampler ports uniform privatePorts R fuel qH) inputWidth _ _ he hb'
  have hd := code_description rep data cost primitive sampler descriptionSizes allowance descriptionLaws descriptionData
    bd boundary ports uniform privatePorts R descriptionDispatch fuel qH
  rw [codeDescription_eq] at hd
  exact Within.mono backend descriptionSizes factor description hw (Nat.mul_le_mul_left factor hd) le_rfl

end Signatures.Runtime.Schnorr.ListROM.NativeSolver
