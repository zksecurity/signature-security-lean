import Signatures.Runtime.BackendSchnorrNonzeroSolver
import Signatures.Runtime.BackendSchnorrNonzeroForkBudget
import Signatures.Runtime.BackendSchnorrROMSolverSetup

/-! Complete native solver runtime from original attacker/sampler resources and
primitive contracts. Setup, both fork runs, extraction, fallback and all routing
are derived internally; no finished component budget is assumed. -/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.Schnorr.NonzeroListROM.NativeSolver

open BackendProgram RawTape ListROM ListROM.NativeInterface ListROM.NativeComponents ListROM.NativeSolver

def resourcesTime (overhead : Nat → Nat) (bound : ExecutionCost)
    (width tapeWidth managedCap liveCap fuel : Nat) (first second : NativePass.TimeInputs)
    (scaleTime addTime messageTime pointTime incrementTime comparisonTime scalarComparisonTime subtractTime
      extractionScalarTime fieldSubTime divTime : Nat) : Nat :=
  NativeROMFork.resourcesTime overhead bound width tapeWidth managedCap liveCap fuel first second
    scaleTime addTime messageTime pointTime incrementTime comparisonTime scalarComparisonTime subtractTime +
  NativeExtraction.runtimeBound overhead width managedCap (liveCap + 1) pointTime extractionScalarTime fieldSubTime divTime
    first.zeroTime (ExecutionProfile.runtimeBound overhead tapeWidth first.fieldWork first.fieldVisits first.fieldQueries first.tickTime first.queryTime) +
  128 * overhead (8192 * NativeExtraction.frameWidth width managedCap (liveCap + 1))

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {F G₁ G₂ K M : Type}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))

variable {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)

variable [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum] [Q.IsDistributive]
  [Q.HasOption] [OptionCode (Q := Q)]
  [Field F] [SampleableType F] [SampleableType Fˣ]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  {iface : Interface (C := C) unifSpec}
  (bd : Boundary C (sourceSpec F G₁ M).toPFunctor G₁ (M × G₁ × F))
  (boundary : ListROM.NativePass.DataPorts (Q := Q) rep bd) (ports : Ports (Q := Q) rep bd)
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  (uniform : UniformSampling.Ports (Q := Q) rep.data (iface := iface))
  (privatePorts : NativePrivate.Ports (Q := Q) rep (iface := iface))
  (fieldSampler nonzeroSampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))
  (fieldLaw : fieldSampler.denote () = ($ᵗ F : ProbComp F))
  (nonzeroLaw : nonzeroSampler.denote () = (fun a : Fˣ => (a : F)) <$> ($ᵗ Fˣ))
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
  (mono : Monotone overhead)
  (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
  (routing : RoutingCostLaws control overhead) (dispatch : DispatchCostLaws (Q := Q) overhead)
  (R : GeneralCaller.Caller (Q := Q) (bd := bd))
  (recovery : ListROM.NativeHandler.RequestRecovery (Q := Q) rep bd)
  (bound : ExecutionCost) (hrun : R.RunsWithin (fun _ => bound))

include fieldLaw nonzeroLaw sizes lists laws dataLaws mono routing dispatch hrun

theorem code_bound_of_resources (width tapeWidth managedCap liveCap fuel qH : Nat)
    (first : NativePass.Resources rep bd boundary ports cost primitive uniform privatePorts fieldSampler nonzeroSampler primitiveBound
      control queryCost recovery bound (header := header) width tapeWidth managedCap liveCap 0 0 fuel)
    (second : NativePass.Resources rep bd boundary ports cost primitive uniform privatePorts fieldSampler nonzeroSampler primitiveBound
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
    (hinl : Q.cost (QS.inl rep.data.unit (rep.ty (.pair ListROM.NativePass.outputTy ListROM.NativePass.outputTy))) () ≤
      overhead (Q.size rep.data.unit () +
        Q.size (StepClass.HasSum.sum rep.data.unit (rep.ty (.pair ListROM.NativePass.outputTy ListROM.NativePass.outputTy))) (.inl ())))
    (hinr : ∀ p, Q.cost (QS.inr rep.data.unit (rep.ty (.pair ListROM.NativePass.outputTy ListROM.NativePass.outputTy))) p ≤
      overhead (Q.size (rep.ty (.pair ListROM.NativePass.outputTy ListROM.NativePass.outputTy)) p +
        Q.size (StepClass.HasSum.sum rep.data.unit (rep.ty (.pair ListROM.NativePass.outputTy ListROM.NativePass.outputTy))) (.inr p))) :
    Bounds control queryCost (code rep bd boundary data cost primitive fieldSampler nonzeroSampler ports uniform privatePorts R fuel qH)
      (ListROM.NativeSolver.InputBound (Q := Q) rep width) (fun f => Q.size (rep.ty scalar) f ≤ 3 * width)
      (resourcesTime overhead bound width tapeWidth managedCap liveCap fuel first.timeInputs second.timeInputs
        scaleTime addTime messageTime pointTime incrementTime comparisonTime scalarComparisonTime subtractTime
        extractionScalarTime fieldSubTime divTime) := by
  let W := NativeExtraction.frameWidth width managedCap (liveCap + 1)
  let config := ConfigBound (Q := Q) rep width
  let forkOutput := NativeFork.Result (Q := Q) rep (ListROM.NativeROMFork.controllerWidth width managedCap (liveCap + 1))
    (ListROM.NativeROMFork.ValidOutput (Q := Q) rep width managedCap (liveCap + 1))
  let post := fun f => Q.size (rep.ty scalar) f ≤ 3 * width
  have htw : tapeWidth ≤ width := NativePass.Resources.tapeWidth_le (resources := first)
  have hw : 8 * width ≤ W := by dsimp [W, NativeExtraction.frameWidth]; nlinarith
  have hsetup := setup_bound (iface := iface) rep sizes data cost primitive laws dataLaws primitiveBound mono control queryCost routing
    width (first.hh.trans htw) (first.hu.trans htw)
  have hfork := NativeROMFork.code_bound_of_resources rep sizes lists bd boundary ports data cost primitive uniform privatePorts
    fieldSampler nonzeroSampler fieldLaw nonzeroLaw laws dataLaws primitiveBound mono control queryCost routing dispatch R recovery bound hrun
    width tapeWidth managedCap liveCap fuel qH first second scaleTime addTime messageTime pointTime incrementTime
    comparisonTime scalarComparisonTime subtractTime selectorOps hn hscalar hsub hinl hinr
  have hsample := NativePass.Resources.fieldSampler_bound (resources := first) (sizes := sizes) (mono := mono) (routing := routing)
  have hsampler : Bounds control queryCost fieldSampler (fun _ => True) post
      (ExecutionProfile.runtimeBound overhead tapeWidth first.fieldWork first.fieldVisits first.fieldQueries first.tickTime first.queryTime) :=
    Bounds.consequence control queryCost hsample (fun _ h => h) (fun _ h => h.trans (by omega))
  have hextract := NativeExtraction.code_bound rep data cost primitive fieldSampler sizes lists laws dataLaws primitiveBound mono
    control queryCost routing width managedCap (liveCap + 1) pointTime extractionScalarTime fieldSubTime divTime first.zeroTime
    (ExecutionProfile.runtimeBound overhead tapeWidth first.fieldWork first.fieldVisits first.fieldQueries first.tickTime first.queryTime)
    (first.hh.trans htw) (first.hu.trans htw) (fun b => (first.hb b).trans htw) (first.hz.trans htw) extractionOps hsampler
  have hinput (input) (hi : ListROM.NativeSolver.InputBound (Q := Q) rep width input) : Q.size (rep.env inputTypes) input ≤ W :=
    (input_size rep sizes width (first.hh.trans htw) (first.hu.trans htw) input hi).trans (by omega)
  have hconfig (input) (hi : config input) : Q.size (rep.ty configTy) input ≤ W :=
    (config_size rep sizes width (first.hh.trans htw) input hi).trans (by omega)
  have hresult (result) (hi : forkOutput result) :
      Q.size (StepClass.HasSum.sum rep.data.unit (rep.ty NativeExtraction.inputTy)) result ≤ W := by
    have hs := sizes.sum_le rep.data.unit (rep.ty NativeExtraction.inputTy) result
    have hh := first.hh.trans htw
    have hu := first.hu.trans htw
    cases result with
    | inl u =>
        cases u
        change Q.size (StepClass.HasSum.sum rep.data.unit (rep.ty NativeExtraction.inputTy)) (.inl ()) ≤
          Q.size rep.data.unit () + header at hs
        change Q.size (StepClass.HasSum.sum rep.data.unit (rep.ty NativeExtraction.inputTy)) (.inl ()) ≤ W
        omega
    | inr pair =>
        have hf := hi.1.2
        have hr := hi.2.2
        have hp := sizes.prod_le (rep.ty ListROM.NativePass.outputTy) (rep.ty ListROM.NativePass.outputTy) pair
        change Q.size (rep.ty NativeExtraction.inputTy) pair ≤ _ at hp
        dsimp only [Sum.elim] at hs
        dsimp only [W, NativeExtraction.frameWidth, ListROM.NativeROMFork.controllerWidth] at *
        nlinarith only [hf, hr, hp, hs, hh]
  have hterminal := seq_bound_of_width mono control queryCost routing _ _ config forkOutput post W _ _
    hconfig hresult hfork hextract
  have hall := seq_bound_of_width mono control queryCost routing _ _ (ListROM.NativeSolver.InputBound (Q := Q) rep width) config post W _ _
    hinput hconfig hsetup hterminal
  have hsmall := mono (show 256 * width ≤ 8192 * W by omega)
  have hseq := mono (show 32 * W ≤ 8192 * W by omega)
  apply Bounds.time_mono control queryCost hall
  change 65 * overhead (256 * width) + (_ + _ + overhead (32 * W)) + overhead (32 * W) ≤
    _ + _ + 128 * overhead (8192 * W)
  dsimp only [NativePass.Resources.timeInputs]
  omega

end Signatures.Runtime.Schnorr.NonzeroListROM.NativeSolver
