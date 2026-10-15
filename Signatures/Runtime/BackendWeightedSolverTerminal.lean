import Signatures.Runtime.BackendWeightedSolverTerminalBudget
import Signatures.Runtime.BackendWeightedSolverContracts
import Signatures.Runtime.BackendWeightedGoodExtractionBudget
import Signatures.Runtime.BackendWeightedBadExtractionBudget

/-! Complete native terminal bounds for weighted extraction. Runtime, full input
and coefficient sizes are derived from primitive contracts, the output encoding,
and the interaction's preserved cache/log invariants. -/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.WeightedAGM.NativeSolver

open BackendProgram NativeHandler Reply

def goodTerminalTime (index : Index) (overhead : Nat → Nat)
    (width outputWidth routeWidth cap comparisonTime scalarTime opTime adapterTime tickTime : Nat) : Nat :=
  Extract.goodExtractionTime index overhead (extractionEntryWidth width cap outputWidth) cap cap outputWidth
    (cap * (index.bound + 1)) opTime opTime opTime comparisonTime opTime scalarTime opTime opTime opTime tickTime
    opTime opTime opTime opTime opTime +
    opTime + 2 * adapterTime + 160 * overhead (4096 * terminalFrameWidth index width outputWidth routeWidth cap)

def badTerminalTime (index : Index) (overhead : Nat → Nat)
    (width outputWidth routeWidth cap comparisonTime scalarTime opTime adapterTime tickTime : Nat) : Nat :=
  Extract.badExtractionTime index overhead (extractionEntryWidth width cap outputWidth) cap cap outputWidth
    (cap * (index.bound + 1)) opTime opTime opTime comparisonTime opTime scalarTime opTime opTime opTime tickTime
    opTime opTime opTime opTime opTime opTime +
    opTime + 2 * adapterTime + 160 * overhead (4096 * terminalFrameWidth index width outputWidth routeWidth cap)

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum] [QO : Q.HasOption]
  [QD : Q.IsDistributive] [OC : OptionCode (Q := Q)]
  {F G₁ G₂ K M : Type} [Field F] [SampleableType F]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq K] [DecidableEq M]
  {iface : Interface (C := C) unifSpec} {randomBound : Nat}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (index : Index)
  (bd : Boundary C (generalSpec (index.ty.Value (cryptoBase F G₁ G₂ K M)) (index.messageTy.Value (cryptoBase F G₁ G₂ K M)) G₁ randomBound).toPFunctor G₂
    ((AGM.outputTy index.messageTy).Value (cryptoBase F G₁ G₂ K M)))
  (boundary : DataPorts (Q := Q) rep index bd)
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  (sampling : MachineCompiler.SamplingImplementation Q iface rep)
  (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)
  (lengths : ListLengthLaws Q rep.data)
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
  (mono : Monotone overhead) (routing : RoutingCostLaws control overhead)
  (dispatch : DispatchCostLaws (Q := Q) overhead)

include sizes lists lengths laws dataLaws primitiveBound mono routing dispatch

theorem goodTerminal_bound (width outputWidth routeWidth cap keyWidth
    comparisonTime scalarTime opTime adapterTime tickTime : Nat)
    (hh : header ≤ width) (values : ValueCaps (Q := Q) rep index width cap)
    (ops : OperationCaps rep index cost primitive primitiveBound cap keyWidth opTime comparisonTime)
    (caps : PortCaps rep index bd boundary width outputWidth routeWidth adapterTime)
    (hcomparison : 3 * Extract.extractionWidth index (extractionEntryWidth width cap outputWidth)
      cap cap outputWidth (cap * (index.bound + 1)) ≤ keyWidth)
    (hsample : ∀ z ∈ support (sampling.scalar.run control queryCost ()), z.steps ≤ scalarTime)
    (htick : ∀ n ≤ rowCap index cap, ∀ encoded ≤ 7 * Extract.extractionWidth index
      (extractionEntryWidth width cap outputWidth) cap cap outputWidth (cap * (index.bound + 1)),
      control.loop n encoded ≤ tickTime) :
    Bounds control queryCost (terminal rep index bd boundary data cost primitive scalar LazyAGM.goodConfigTy
      (Extract.backendGood rep data cost primitive sampling index))
      (fun p => ResultReady (Q := Q) index bd routeWidth p.1 ∧ ExtractionReady (Q := Q) rep index cost scalar LazyAGM.goodConfigTy width cap p.2)
      (fun out => Q.size (rep.ty scalar) out ≤ width)
      (goodTerminalTime index overhead width outputWidth routeWidth cap comparisonTime scalarTime opTime adapterTime tickTime) := by
  let E := extractionEntryWidth width cap outputWidth
  let W := terminalFrameWidth index width outputWidth routeWidth cap
  have hwE : width ≤ E := by have h := extractionEntryWidth_ge width cap outputWidth; omega
  have hEW : E ≤ W := by dsimp [W, terminalFrameWidth, E]; omega
  have hEW' : Extract.extractionWidth index E cap cap outputWidth (cap * (index.bound + 1)) ≤ W := by
    dsimp [W, terminalFrameWidth, E]; omega
  have hwW := hwE.trans hEW
  have hstore : ∀ saved, ExtractionReady (Q := Q) rep index cost scalar LazyAGM.goodConfigTy width cap saved →
      Q.size (rep.ty (storeTy index.ty index.messageTy scalar LazyAGM.goodConfigTy)) saved ≤ W := by
    intro saved hs
    exact (goodReserved_size rep index sizes lists width cap 0 hh values.scalar values.point₁ saved hs.1).trans
      (by dsimp [W, terminalFrameWidth]; omega)
  have h := terminal_bound_of_extractor rep index bd boundary data cost primitive control queryCost sizes laws dataLaws
    primitiveBound mono routing dispatch scalar LazyAGM.goodConfigTy (Extract.backendGood rep data cost primitive sampling index)
    (ExtractionReady (Q := Q) rep index cost scalar LazyAGM.goodConfigTy width cap) W width outputWidth routeWidth adapterTime
    (Extract.goodExtractionTime index overhead E cap cap outputWidth (cap * (index.bound + 1))
      opTime opTime opTime comparisonTime opTime scalarTime opTime opTime opTime tickTime opTime opTime opTime opTime opTime) opTime
    (hh.trans hwW) (values.unit.trans hwW)
    (by dsimp [W, terminalFrameWidth, extractionEntryWidth]; omega)
    (by dsimp [W, terminalFrameWidth]; omega) ((values.scalar 0).trans hwW) ops.zero caps hstore (by
      intro out saved ho hs z hz
      have ready := extractionEntry_bounds rep sizes lists lengths index out saved width cap outputWidth
        hh values.unit values.point₁ hs.1 ho
      have he := Extract.backendGood_bound rep data cost primitive laws dataLaws primitiveBound sizes lists mono
        control queryCost routing sampling index out saved.2.2 saved.2.1
        E cap cap outputWidth (cap * (index.bound + 1)) opTime opTime opTime comparisonTime opTime scalarTime
        opTime opTime opTime tickTime opTime opTime opTime opTime opTime
        (hh.trans hwE) (values.unit.trans hwE) (fun b => (values.bool b).trans hwE)
        (fun n hn => (values.nat n hn).trans hwE) (fun f => (values.scalar f).trans hwE)
        ready.1 ready.2.1 ready.2.2.1 (fun j => (values.index j).trans hwE)
        ready.2.2.2.1 ready.2.2.2.2.1 ready.2.2.2.2.2.2.2.1 ready.2.2.2.2.2.2.2.2
        ready.2.2.2.2.2.1 ready.2.2.2.2.2.2.1 hs.2
        ops.natEq ops.natSub ops.natAdd
        (fun x y hx hy => ops.keyEq x y (hx.trans hcomparison) (hy.trans hcomparison))
        ops.finVal hsample ops.zero ops.add ops.mul htick ops.finOfNat ops.finZero ops.one ops.sub ops.div z hz
      exact ⟨⟨(values.scalar _).trans hwW, he.1.2.trans hEW'⟩, he.2⟩)
  intro input hi z hz
  exact ⟨values.scalar _, (h input hi z hz).2⟩

theorem badTerminal_bound (width outputWidth routeWidth cap keyWidth
    comparisonTime scalarTime opTime adapterTime tickTime : Nat)
    (hh : header ≤ width) (values : ValueCaps (Q := Q) rep index width cap)
    (ops : OperationCaps rep index cost primitive primitiveBound cap keyWidth opTime comparisonTime)
    (caps : PortCaps rep index bd boundary width outputWidth routeWidth adapterTime)
    (hcomparison : 3 * Extract.extractionWidth index (extractionEntryWidth width cap outputWidth)
      cap cap outputWidth (cap * (index.bound + 1)) ≤ keyWidth)
    (hsample : ∀ z ∈ support (sampling.scalar.run control queryCost ()), z.steps ≤ scalarTime)
    (htick : ∀ n ≤ rowCap index cap, ∀ encoded ≤ 7 * Extract.extractionWidth index
      (extractionEntryWidth width cap outputWidth) cap cap outputWidth (cap * (index.bound + 1)),
      control.loop n encoded ≤ tickTime) :
    Bounds control queryCost (terminal rep index bd boundary data cost primitive (.pair scalar scalar) LazyAGM.badConfigTy
      (Extract.backendBad rep data cost primitive sampling index))
      (fun p => ResultReady (Q := Q) index bd routeWidth p.1 ∧ ExtractionReady (Q := Q) rep index cost (.pair scalar scalar) LazyAGM.badConfigTy width cap p.2)
      (fun out => Q.size (rep.ty scalar) out ≤ width)
      (badTerminalTime index overhead width outputWidth routeWidth cap comparisonTime scalarTime opTime adapterTime tickTime) := by
  let E := extractionEntryWidth width cap outputWidth
  let W := terminalFrameWidth index width outputWidth routeWidth cap
  have hwE : width ≤ E := by have h := extractionEntryWidth_ge width cap outputWidth; omega
  have hEW : E ≤ W := by dsimp [W, terminalFrameWidth, E]; omega
  have hEW' : Extract.extractionWidth index E cap cap outputWidth (cap * (index.bound + 1)) ≤ W := by
    dsimp [W, terminalFrameWidth, E]; omega
  have hwW := hwE.trans hEW
  have hstore : ∀ saved, ExtractionReady (Q := Q) rep index cost (.pair scalar scalar) LazyAGM.badConfigTy width cap saved →
      Q.size (rep.ty (storeTy index.ty index.messageTy (.pair scalar scalar) LazyAGM.badConfigTy)) saved ≤ W := by
    intro saved hs
    exact (badReserved_size rep index sizes lists width cap 0 hh values.scalar values.point₁ saved hs.1).trans
      (by dsimp [W, terminalFrameWidth]; omega)
  have h := terminal_bound_of_extractor rep index bd boundary data cost primitive control queryCost sizes laws dataLaws
    primitiveBound mono routing dispatch (.pair scalar scalar) LazyAGM.badConfigTy (Extract.backendBad rep data cost primitive sampling index)
    (ExtractionReady (Q := Q) rep index cost (.pair scalar scalar) LazyAGM.badConfigTy width cap) W width outputWidth routeWidth adapterTime
    (Extract.badExtractionTime index overhead E cap cap outputWidth (cap * (index.bound + 1))
      opTime opTime opTime comparisonTime opTime scalarTime opTime opTime opTime tickTime opTime opTime opTime opTime opTime opTime) opTime
    (hh.trans hwW) (values.unit.trans hwW)
    (by dsimp [W, terminalFrameWidth, extractionEntryWidth]; omega)
    (by dsimp [W, terminalFrameWidth]; omega) ((values.scalar 0).trans hwW) ops.zero caps hstore (by
      intro out saved ho hs z hz
      have ready := extractionEntry_bounds rep sizes lists lengths index out saved width cap outputWidth
        hh values.unit values.point₁ hs.1 ho
      have he := Extract.backendBad_bound rep data cost primitive laws dataLaws primitiveBound sizes lists mono
        control queryCost routing sampling index out saved.2.2 saved.2.1
        E cap cap outputWidth (cap * (index.bound + 1)) opTime opTime opTime comparisonTime opTime scalarTime
        opTime opTime opTime tickTime opTime opTime opTime opTime opTime opTime
        (hh.trans hwE) (values.unit.trans hwE) (fun b => (values.bool b).trans hwE)
        (fun n hn => (values.nat n hn).trans hwE) (fun f => (values.scalar f).trans hwE)
        ready.1 ready.2.2.1 (fun j => (values.index j).trans hwE)
        ready.2.2.2.2.1 ready.2.2.2.2.2.2.2.2
        ready.2.2.2.2.2.1 ready.2.2.2.2.2.2.1 hs.2
        ops.natEq ops.natSub ops.natAdd
        (fun x y hx hy => ops.keyEq x y (hx.trans hcomparison) (hy.trans hcomparison))
        ops.finVal hsample ops.zero ops.add ops.mul htick ops.finOfNat ops.finZero ops.one ops.sub ops.neg ops.div z hz
      exact ⟨⟨(values.scalar _).trans hwW, he.1.2.trans hEW'⟩, he.2⟩)
  intro input hi z hz
  exact ⟨values.scalar _, (h input hi z hz).2⟩

end Signatures.Runtime.WeightedAGM.NativeSolver
