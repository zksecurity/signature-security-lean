import Proofs.Runtime.BackendSchnorrAGMSolverTerminalComposition
import Proofs.Runtime.BackendSchnorrAGMExtractionBudget
import Proofs.Runtime.BackendSchnorrAGMExtractionResources

/-! The complete executed Schnorr AGM terminal has a primitive-derived budget.
Return conversion preserves all rows. The extraction contract is recovered from
the measured encoding and caller state; no finished extractor budget is assumed. -/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.SchnorrAGM.Native.Solver

open BackendProgram Interface

def terminalWidth (width outputWidth routeWidth cap basisCap signedCap : Nat) : Nat :=
  width + outputWidth + routeWidth + (60 * cap + 4 * basisCap + 2 * signedCap + 27) * width +
    Read.frameWidth (3 * max width outputWidth) cap (HandlerComponents.historyWidth width basisCap signedCap)

def terminalTime (overhead : Nat → Nat)
    (width outputWidth routeWidth cap basisCap signedCap adapterTime comparisonTime subtractTime incrementTime
      messageTime pointTime fieldTime mulTime equalityTime sampleTime divisionTime pointZeroTime : Nat) : Nat :=
  let E := max width outputWidth
  Extraction.extractionTime overhead E cap (HandlerComponents.historyWidth width basisCap signedCap)
    basisCap E E E comparisonTime subtractTime incrementTime messageTime pointTime fieldTime mulTime equalityTime
      sampleTime divisionTime pointZeroTime + fieldTime + 2 * adapterTime +
    23 * overhead (4096 * terminalWidth width outputWidth routeWidth cap basisCap signedCap)

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum] [Q.HasOption]
  [QD : Q.IsDistributive] [OptionCode (Q := Q)]
  {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  {iface : BackendProgram.Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (bd : Boundary C (sourceSpec F G₁ M).toPFunctor (SourceInput G₁) (SourceForgery F G₁ M))
  (boundary : DataPorts (Q := Q) rep bd)
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  (sampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)
  (lengths : ListLengthLaws Q rep.data) (payloads : ListPayloadLaws Q rep.data)
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
  (mono : Monotone overhead)
  (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
  (routing : RoutingCostLaws control overhead) (dispatch : DispatchCostLaws (Q := Q) overhead)

include sizes lists lengths payloads laws dataLaws primitiveBound mono routing dispatch

theorem terminal_bound (width outputWidth routeWidth cap basisCap signedCap adapterTime
    comparisonTime subtractTime incrementTime messageTime pointTime fieldTime mulTime equalityTime
    sampleTime divisionTime pointZeroTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (caps : PortCaps rep bd boundary width outputWidth routeWidth adapterTime)
    (hn : ∀ n ≤ basisCap + 1, Q.size rep.data.nat n ≤ max width outputWidth)
    (hEq : ∀ n ≤ basisCap, (primitiveBound .natEq).time (n, 0) ≤ comparisonTime)
    (hSub : ∀ n ≤ basisCap, (primitiveBound .natSub).time (n, 1) ≤ subtractTime)
    (hInc : ∀ n ≤ basisCap, (primitiveBound .natAdd).time (n, 1) ≤ incrementTime)
    (hm : ∀ a b : M, Q.size (rep.ty message) a ≤ 15 * max width outputWidth →
      Q.size (rep.ty message) b ≤ 15 * max width outputWidth → (primitiveBound .messageEq).time (a, b) ≤ messageTime)
    (hg : ∀ a b : G₁, Q.size (rep.ty point₁) a ≤ 15 * max width outputWidth →
      Q.size (rep.ty point₁) b ≤ 15 * max width outputWidth → (primitiveBound .point₁Eq).time (a, b) ≤ pointTime)
    (hz : (primitiveBound .zero).time () ≤ fieldTime)
    (hadd : ∀ a b : F, (primitiveBound .add).time (a, b) ≤ fieldTime)
    (hmul : ∀ a b : F, (primitiveBound .mul).time (a, b) ≤ mulTime)
    (heq : ∀ a b : F, (primitiveBound .scalarEq).time (a, b) ≤ equalityTime)
    (hd : Bounds control queryCost sampler (fun _ => True)
      (fun c => Q.size (rep.ty scalar) c ≤ max width outputWidth) sampleTime)
    (hsub : ∀ a b : F, (primitiveBound .sub).time (a, b) ≤ fieldTime)
    (hdiv : ∀ a b : F, (primitiveBound .div).time (a, b) ≤ divisionTime)
    (hg0 : Q.size (rep.ty point₁) (0 : G₁) ≤ max width outputWidth)
    (hz0 : (primitiveBound .zero₁).time () ≤ pointZeroTime) :
    Bounds control queryCost (terminal rep bd boundary data cost primitive (Extraction.code rep data cost primitive sampler))
      (fun p => ResultReady (Q := Q) bd routeWidth p.1 ∧
        HandlerComponents.StoreBound (Q := Q) rep width cap basisCap signedCap p.2)
      (fun out => Q.size (rep.ty scalar) out ≤ terminalWidth width outputWidth routeWidth cap basisCap signedCap)
      (terminalTime overhead width outputWidth routeWidth cap basisCap signedCap adapterTime
        comparisonTime subtractTime incrementTime messageTime pointTime fieldTime mulTime equalityTime
        sampleTime divisionTime pointZeroTime) := by
  let E := max width outputWidth
  let H := HandlerComponents.historyWidth width basisCap signedCap
  let W := terminalWidth width outputWidth routeWidth cap basisCap signedCap
  let keep := Signing.StateBound (Q := Q) rep width cap basisCap signedCap
  have hwE : width ≤ E := le_max_left _ _
  have hw : width ≤ W := by dsimp only [W, terminalWidth]; omega
  have ho : outputWidth ≤ W := by dsimp only [W, terminalWidth]; omega
  have hr : routeWidth ≤ W := by dsimp only [W, terminalWidth]; omega
  have hresult : Read.frameWidth (3 * E) cap H ≤ W := by dsimp only [W, E, H, terminalWidth]; omega
  have he := Extraction.bound rep data cost primitive sizes lists laws dataLaws primitiveBound mono control queryCost routing dispatch
    E cap H basisCap E E E (hh.trans hwE) (hu.trans hwE) (fun b => (hb b).trans hwE) (fun f => (hf f).trans hwE)
    sampler comparisonTime subtractTime incrementTime messageTime pointTime fieldTime mulTime equalityTime sampleTime divisionTime pointZeroTime
    hn hEq hSub hInc hm hg hz hadd hmul heq hd hsub hdiv hg0 hz0
  have he' : Bounds control queryCost (Extraction.code rep data cost primitive sampler)
      (fun p => Q.size (rep.ty forgeryTy) p.1 ≤ outputWidth ∧ Q.size (rep.ty stateTy) p.2 ≤ W ∧ keep p.2)
      (fun p => Q.size (rep.ty Read.outputTy) p ≤ W)
      (Extraction.extractionTime overhead E cap H basisCap E E E comparisonTime subtractTime incrementTime
        messageTime pointTime fieldTime mulTime equalityTime sampleTime divisionTime pointZeroTime) := by
    intro p hp z hz'
    have hi := Extraction.input_of_state rep sizes lengths payloads lists width outputWidth cap basisCap signedCap
      hh hb hf (decodeForgery p.1) p.2 (by simpa only [encode_decodeForgery] using hp.1) hp.2.2
    rw [encode_decodeForgery] at hi
    obtain ⟨hout, ht⟩ := he p hi z hz'
    exact ⟨(Read.output_size rep sizes lists (3 * E) cap H (by omega)
      (fun b => (hb b).trans (by omega)) z.value hout).trans hresult, ht⟩
  have hall := terminal_bound_of_extractor rep bd boundary sizes laws mono control queryCost routing data cost primitive
    dataLaws primitiveBound dispatch (Extraction.code rep data cost primitive sampler) keep
    W width routeWidth outputWidth adapterTime _ fieldTime (hh.trans hw) (hu.trans hw) hr ho ((hf 0).trans hw) hz caps he'
  intro input hi z hz'
  have hs := HandlerComponents.store_size rep sizes lists width cap basisCap signedCap hh hb hf input.2 hi.2
  have hstore : Q.size (rep.ty storeTy) input.2 ≤ W := hs.trans (by dsimp only [W, terminalWidth]; omega)
  exact hall input ⟨hi.1, hstore, hi.2.state⟩ z hz'

end Signatures.Runtime.SchnorrAGM.Native.Solver
