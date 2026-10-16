import Signatures.Runtime.BackendSchnorrNonzeroFork
import Signatures.Runtime.BackendSchnorrNonzeroPassResources
import Signatures.Runtime.BackendSchnorrROMForkBudget
import Signatures.Runtime.BackendSchnorrRawForkBudget

/-! Complete runtime of the installed nonzero-nonce ROM fork. Both pass budgets,
selection and replacement sampling are derived from original resources. Narrow
tape entries remain separate from the retained configuration/output footprint. -/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.Schnorr.NonzeroListROM.NativeROMFork

open BackendProgram RawTape ListROM ListROM.NativeInterface ListROM.NativeComponents ListROM.NativeROMFork

/-- The complete installed runtime, expanded from original component resources.
The replay reservation includes the first pass's final hash and reset cell. -/
def resourcesTime (overhead : Nat → Nat) (bound : ExecutionCost)
    (width tapeWidth managedCap liveCap fuel : Nat) (first second : NativePass.TimeInputs)
    (scaleTime addTime messageTime pointTime incrementTime comparisonTime scalarComparisonTime subtractTime : Nat) : Nat :=
  NativeFork.runtimeBoundWithTapeWidth overhead (controllerWidth width managedCap (liveCap + 1)) tapeWidth
    (first.savedCap + 1) (second.savedCap + 1)
    (first.time overhead bound width tapeWidth managedCap liveCap 0 fuel)
    (second.time overhead bound width tapeWidth managedCap liveCap (first.savedCap + 2) fuel)
    (NativeSelection.timeBudget overhead width managedCap (liveCap + 1)
      scaleTime addTime messageTime pointTime incrementTime comparisonTime)
    (ExecutionProfile.runtimeBound overhead tapeWidth first.fieldWork first.fieldVisits first.fieldQueries first.tickTime first.queryTime)
    first.comparisonTime scalarComparisonTime subtractTime first.zeroTime

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
    (scaleTime addTime messageTime pointTime incrementTime comparisonTime scalarComparisonTime subtractTime : Nat)
    (selectorOps : NativeSelection.Operations rep cost primitive primitiveBound width (liveCap + 1) qH
      scaleTime addTime messageTime pointTime incrementTime comparisonTime)
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
      (ConfigBound (Q := Q) rep width)
      (NativeFork.Result (Q := Q) rep (controllerWidth width managedCap (liveCap + 1))
        (ValidOutput (Q := Q) rep width managedCap (liveCap + 1)))
      (resourcesTime overhead bound width tapeWidth managedCap liveCap fuel first.timeInputs second.timeInputs
        scaleTime addTime messageTime pointTime incrementTime comparisonTime scalarComparisonTime subtractTime) := by
  let W := controllerWidth width managedCap (liveCap + 1)
  let validOut := ValidOutput (Q := Q) rep width managedCap (liveCap + 1)
  let validConfig := ConfigBound (Q := Q) rep width
  have htw : tapeWidth ≤ width := NativePass.Resources.tapeWidth_le (resources := first)
  have hw : width ≤ W := by dsimp [W, controllerWidth]; nlinarith
  have hfirstPass := NativePass.Resources.pass_bound (resources := first) (data := data) (fieldLaw := fieldLaw) (nonzeroLaw := nonzeroLaw)
    (sizes := sizes) (lists := lists) (laws := laws) (dataLaws := dataLaws) (mono := mono)
    (routing := routing) (dispatch := dispatch) (R := R) (hrun := hrun)
  have hsecondPass := NativePass.Resources.pass_bound (resources := second) (data := data) (fieldLaw := fieldLaw) (nonzeroLaw := nonzeroLaw)
    (sizes := sizes) (lists := lists) (laws := laws) (dataLaws := dataLaws) (mono := mono)
    (routing := routing) (dispatch := dispatch) (R := R) (hrun := hrun)
  have hfirst : Bounds control queryCost
      (NativePass.code rep bd boundary data cost primitive fieldSampler nonzeroSampler ports uniform privatePorts R fuel)
      (NativeFork.IncomingWidths (Q := Q) rep W tapeWidth 0 0 validConfig)
      (NativeFork.ReturnedWidths (Q := Q) rep W tapeWidth (first.savedCap + 1) 0 validOut) (first.time overhead) := by
    intro input hi z hz
    obtain ⟨ho, ht⟩ := hfirstPass input ⟨hi.2.1, hi.1⟩ z hz
    have hv : validOut z.value.1 := ⟨ho.results, ho.length⟩
    exact ⟨⟨⟨hv, output_size rep sizes lists width managedCap (liveCap + 1)
      (first.hh.trans htw) z.value.1 hv⟩, ho.tape⟩, ht⟩
  have hsecond : Bounds control queryCost
      (NativePass.code rep bd boundary data cost primitive fieldSampler nonzeroSampler ports uniform privatePorts R fuel)
      (NativeFork.IncomingWidths (Q := Q) rep W tapeWidth (first.savedCap + 2) (first.savedCap + 2) validConfig)
      (NativeFork.ReturnedWidths (Q := Q) rep W tapeWidth (second.savedCap + 1) (first.savedCap + 2) validOut)
      (second.time overhead) := by
    intro input hi z hz
    obtain ⟨ho, ht⟩ := hsecondPass input ⟨hi.2.1, hi.1⟩ z hz
    have hv : validOut z.value.1 := ⟨ho.results, ho.length⟩
    exact ⟨⟨⟨hv, output_size rep sizes lists width managedCap (liveCap + 1)
      (first.hh.trans htw) z.value.1 hv⟩, ho.tape⟩, ht⟩
  have hselect : ∀ xs, NativeFork.Ready (Q := Q) rep W validOut xs →
      Q.cost (NativeSelection.selector rep data cost primitive qH) xs ≤
        NativeSelection.timeBudget overhead width managedCap (liveCap + 1)
          scaleTime addTime messageTime pointTime incrementTime comparisonTime := by
    intro xs hx
    exact NativeSelection.selector_cost rep data cost primitive sizes lists laws dataLaws primitiveBound mono
      xs width managedCap (liveCap + 1) qH scaleTime addTime messageTime pointTime incrementTime comparisonTime
      (first.hh.trans htw) (first.hu.trans htw) (fun b => (first.hb b).trans htw)
      (fun n hn' => (hn n hn').trans htw) hx.1.1 hx.1.2 selectorOps
  have hsample := NativePass.Resources.fieldSampler_bound (resources := first)
    (sizes := sizes) (mono := mono) (routing := routing)
  have hall := NativeFork.bound_with_tapeWidth rep data cost primitive
    (NativeSelection.selector rep data cost primitive qH)
    (NativePass.code rep bd boundary data cost primitive fieldSampler nonzeroSampler ports uniform privatePorts R fuel) fieldSampler
    sizes lists laws dataLaws primitiveBound mono control queryCost routing validConfig validOut
    W tapeWidth (first.savedCap + 1) (second.savedCap + 1) qH (first.time overhead) (second.time overhead)
    (NativeSelection.timeBudget overhead width managedCap (liveCap + 1)
      scaleTime addTime messageTime pointTime incrementTime comparisonTime)
    (ExecutionProfile.runtimeBound overhead tapeWidth first.fieldWork first.fieldVisits first.fieldQueries first.tickTime first.queryTime)
    first.comparisonTime scalarComparisonTime subtractTime first.zeroTime
    (htw.trans hw) first.hh first.hu first.hb first.hz (hn 0 (by omega)) (hn 1 (by omega))
    (fun n hn' => hn n (by omega)) first.hcompare hscalar hsub first.hzero hinl hinr hfirst hsecond hselect
    (fun xs _ => NativeSelection.value_index_le qH xs) hsample
  intro input hi z hz
  apply hall input ?_ z hz
  refine ⟨hi, ?_⟩
  have hc := config_size rep sizes width (first.hh.trans htw) input hi
  apply hc.trans
  dsimp [W, controllerWidth]
  nlinarith

end Signatures.Runtime.Schnorr.NonzeroListROM.NativeROMFork
