import Proofs.Runtime.BackendLazyAGMSolverTerminalBudget
import Proofs.Runtime.BackendLazyAGMSolverContracts
import Proofs.Runtime.BackendLazyAGMGoodExtractionBudget
import Proofs.Runtime.BackendLazyAGMBadExtractionBudget

/-! Closed native terminal bounds for both AGM solvers. Extractor budgets are
derived from individual operations; input/counter/coefficient capacities follow
from the caller state and full output encoding. No complete-extractor budget or
separate attacker coefficient-length premise remains. -/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.LazyAGM.NativeSolver

open BackendProgram Coron NativeHandler

def goodTerminalTime (overhead : Nat → Nat) (width outputWidth routeWidth cap
    comparisonTime scalarTime opTime adapterTime tickTime : Nat) : Nat :=
  goodExtractionTime overhead (terminalInputWidth width outputWidth cap) cap outputWidth cap
    opTime opTime opTime comparisonTime scalarTime opTime opTime opTime opTime opTime opTime tickTime +
    opTime + 2 * adapterTime + 160 * overhead (4096 * terminalFrameWidth width outputWidth routeWidth cap)

def badTerminalTime (overhead : Nat → Nat) (width outputWidth routeWidth cap
    comparisonTime scalarTime opTime adapterTime tickTime : Nat) : Nat :=
  badExtractionTime overhead (terminalInputWidth width outputWidth cap) cap outputWidth cap
    opTime opTime opTime comparisonTime scalarTime opTime opTime opTime opTime opTime opTime opTime tickTime +
    opTime + 2 * adapterTime + 160 * overhead (4096 * terminalFrameWidth width outputWidth routeWidth cap)

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum] [QO : Q.HasOption]
  [QD : Q.IsDistributive] [OC : OptionCode (Q := Q)]
  {F G₁ G₂ M : Type} [Field F] [SampleableType F]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq M]
  {iface : Interface (C := C) unifSpec} {randomBound : Nat}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ M M))
  (bd : Boundary C (generalSpec M G₁ randomBound).toPFunctor G₂
    ((AGM.outputTy message).Value (cryptoBase F G₁ G₂ M M)))
  (boundary : DataPorts (Q := Q) rep bd)
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ M M cost).execute instr))
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

theorem goodTerminal_bound (width outputWidth routeWidth cap messageWidth
    comparisonTime scalarTime opTime adapterTime tickTime : Nat)
    (hh : header ≤ width) (values : ValueCaps (Q := Q) rep width cap)
    (ops : OperationCaps rep cost primitive primitiveBound cap messageWidth opTime comparisonTime)
    (caps : PortCaps rep bd boundary width outputWidth routeWidth adapterTime)
    (hcomparison : 3 * extractionWidth (terminalInputWidth width outputWidth cap) cap outputWidth cap ≤ messageWidth)
    (hsample : ∀ z ∈ support (sampling.scalar.run control queryCost ()), z.steps ≤ scalarTime)
    (htick : ∀ n ≤ cap, ∀ encoded ≤ 7 * extractionWidth (terminalInputWidth width outputWidth cap) cap outputWidth cap,
      control.loop n encoded ≤ tickTime) :
    Bounds control queryCost (terminal rep bd boundary data cost primitive scalar goodConfigTy
      (backendExtractGood rep data cost primitive sampling))
      (fun p => ResultReady (Q := Q) bd routeWidth p.1 ∧ ReservedState (Q := Q) rep width cap 0 p.2)
      (fun out => Q.size (rep.ty scalar) out ≤ width)
      (goodTerminalTime overhead width outputWidth routeWidth cap comparisonTime scalarTime opTime adapterTime tickTime) := by
  let E := terminalInputWidth width outputWidth cap
  let W := terminalFrameWidth width outputWidth routeWidth cap
  have hwE : width ≤ E := terminalInputWidth_base width outputWidth cap
  have hEW : E ≤ W := by dsimp [W, terminalFrameWidth, E]; omega
  have hEW' : extractionWidth E cap outputWidth cap ≤ W := by dsimp [W, terminalFrameWidth, E]; omega
  have hwW := hwE.trans hEW
  have hstore : ∀ saved, ReservedState (Q := Q) rep width cap 0 saved →
      Q.size (rep.ty (storeTy scalar goodConfigTy)) saved ≤ W := by
    intro saved hs
    exact (goodReserved_size rep sizes lists width cap 0 hh values.scalar values.point₁ saved hs).trans
      (by dsimp [W, terminalFrameWidth, terminalInputWidth]; omega)
  have h := terminal_bound_of_extractor rep bd boundary data cost primitive control queryCost sizes laws dataLaws
    primitiveBound mono routing dispatch scalar goodConfigTy (backendExtractGood rep data cost primitive sampling)
    (ReservedState (Q := Q) rep width cap 0) W width outputWidth routeWidth adapterTime
    (goodExtractionTime overhead E cap outputWidth cap opTime opTime opTime comparisonTime scalarTime
      opTime opTime opTime opTime opTime opTime tickTime) opTime
    (hh.trans hwW) (values.unit.trans hwW) (by dsimp [W, terminalFrameWidth, terminalInputWidth]; omega)
    (by dsimp [W, terminalFrameWidth]; omega) ((values.scalar 0).trans hwW) ops.zero caps hstore (by
      intro out saved ho hs z hz
      have hstored := goodReserved_size rep sizes lists width cap 0 hh values.scalar values.point₁ saved hs
      have ready := extraction_input_caps rep sizes lengths scalar goodConfigTy width outputWidth cap
        hh values.unit values.point₁ out saved ho hs hstored
      have he := backendExtractGood_bound rep data cost primitive laws dataLaws primitiveBound sizes lists mono
        control queryCost routing sampling out saved.2.2 saved.2.1 E cap outputWidth cap
        opTime opTime opTime comparisonTime scalarTime opTime opTime opTime opTime opTime opTime tickTime
        (hh.trans hwE) (values.unit.trans hwE) (fun b => (values.bool b).trans hwE)
        (fun n hn => (values.nat n hn).trans hwE) (fun f => (values.scalar f).trans hwE)
        ((values.point₁ 0).trans hwE) ready.environment ready.tokens ready.transcript ready.coefficients
        ready.cached ready.keys ops.natEq ops.natSub ops.natAdd
        (fun x y hx hy => ops.messageEq x y (hx.trans hcomparison) (hy.trans hcomparison))
        hsample ops.zero ops.groupZero ops.add ops.mul ops.sub ops.div htick z hz
      exact ⟨⟨he.1.1.trans hEW, he.1.2.1.trans hEW'⟩, he.2⟩)
  intro input hi z hz
  exact ⟨values.scalar z.value, (h input hi z hz).2⟩

theorem badTerminal_bound (width outputWidth routeWidth cap messageWidth
    comparisonTime scalarTime opTime adapterTime tickTime : Nat)
    (hh : header ≤ width) (values : ValueCaps (Q := Q) rep width cap)
    (ops : OperationCaps rep cost primitive primitiveBound cap messageWidth opTime comparisonTime)
    (caps : PortCaps rep bd boundary width outputWidth routeWidth adapterTime)
    (hcomparison : 3 * extractionWidth (terminalInputWidth width outputWidth cap) cap outputWidth cap ≤ messageWidth)
    (hsample : ∀ z ∈ support (sampling.scalar.run control queryCost ()), z.steps ≤ scalarTime)
    (htick : ∀ n ≤ cap, ∀ encoded ≤ 7 * extractionWidth (terminalInputWidth width outputWidth cap) cap outputWidth cap,
      control.loop n encoded ≤ tickTime) :
    Bounds control queryCost (terminal rep bd boundary data cost primitive (.pair scalar scalar) badConfigTy
      (backendExtractBad rep data cost primitive sampling))
      (fun p => ResultReady (Q := Q) bd routeWidth p.1 ∧ ReservedState (Q := Q) rep width cap 0 p.2)
      (fun out => Q.size (rep.ty scalar) out ≤ width)
      (badTerminalTime overhead width outputWidth routeWidth cap comparisonTime scalarTime opTime adapterTime tickTime) := by
  let E := terminalInputWidth width outputWidth cap
  let W := terminalFrameWidth width outputWidth routeWidth cap
  have hwE : width ≤ E := terminalInputWidth_base width outputWidth cap
  have hEW : E ≤ W := by dsimp [W, terminalFrameWidth, E]; omega
  have hEW' : extractionWidth E cap outputWidth cap ≤ W := by dsimp [W, terminalFrameWidth, E]; omega
  have hwW := hwE.trans hEW
  have hstore : ∀ saved, ReservedState (Q := Q) rep width cap 0 saved →
      Q.size (rep.ty (storeTy (.pair scalar scalar) badConfigTy)) saved ≤ W := by
    intro saved hs
    exact (badReserved_size rep sizes lists width cap 0 hh values.scalar values.point₁ saved hs).trans
      (by dsimp [W, terminalFrameWidth, terminalInputWidth]; omega)
  have h := terminal_bound_of_extractor rep bd boundary data cost primitive control queryCost sizes laws dataLaws
    primitiveBound mono routing dispatch (.pair scalar scalar) badConfigTy (backendExtractBad rep data cost primitive sampling)
    (ReservedState (Q := Q) rep width cap 0) W width outputWidth routeWidth adapterTime
    (badExtractionTime overhead E cap outputWidth cap opTime opTime opTime comparisonTime scalarTime
      opTime opTime opTime opTime opTime opTime opTime tickTime) opTime
    (hh.trans hwW) (values.unit.trans hwW) (by dsimp [W, terminalFrameWidth, terminalInputWidth]; omega)
    (by dsimp [W, terminalFrameWidth]; omega) ((values.scalar 0).trans hwW) ops.zero caps hstore (by
      intro out saved ho hs z hz
      have hstored := badReserved_size rep sizes lists width cap 0 hh values.scalar values.point₁ saved hs
      have ready := extraction_input_caps rep sizes lengths (.pair scalar scalar) badConfigTy width outputWidth cap
        hh values.unit values.point₁ out saved ho hs hstored
      have he := backendExtractBad_bound rep data cost primitive laws dataLaws primitiveBound sizes lists mono
        control queryCost routing sampling out saved.2.2 saved.2.1 E cap outputWidth cap
        opTime opTime opTime comparisonTime scalarTime opTime opTime opTime opTime opTime opTime opTime tickTime
        (hh.trans hwE) (values.unit.trans hwE) (fun b => (values.bool b).trans hwE)
        (fun n hn => (values.nat n hn).trans hwE) (fun f => (values.scalar f).trans hwE)
        ((values.point₁ 0).trans hwE) ready.environment
        (fun p hp => ready.tokens p (List.mem_append_right _ hp)) ready.transcript.2 ready.coefficients.2
        ready.cached ready.keys ops.natEq ops.natSub ops.natAdd
        (fun x y hx hy => ops.messageEq x y (hx.trans hcomparison) (hy.trans hcomparison))
        hsample ops.zero ops.groupZero ops.add ops.mul ops.sub ops.neg ops.div htick z hz
      exact ⟨⟨he.1.1.trans hEW, he.1.2.1.trans hEW'⟩, he.2⟩)
  intro input hi z hz
  exact ⟨values.scalar z.value, (h input hi z hz).2⟩

end Signatures.Runtime.LazyAGM.NativeSolver
