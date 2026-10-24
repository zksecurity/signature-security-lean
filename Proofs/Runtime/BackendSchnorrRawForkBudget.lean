import Proofs.Runtime.BackendSchnorrRawForkLocalCost
import Proofs.Runtime.BackendSchnorrRawForkTapeWidth

/-! Complete all-path runtime of the native retained-tape fork controller.
The two passes, selector and fresh sampler are actual supplied backend code.
All other work is derived from primitive and structural contracts, including
lookup, reset, adapters, branches, copying and retention of the first result. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.Schnorr.RawTape.NativeFork

open BackendProgram

def runtimeBound (overhead : Nat → Nat)
    (width firstCap secondCap firstTime secondTime selectorTime sampleTime
      comparisonTime scalarComparisonTime subtractTime zeroTime : Nat) : Nat :=
  firstTime + secondTime + 2 * selectorTime + sampleTime +
    NativeLookup.runtimeBound overhead width firstCap comparisonTime subtractTime zeroTime +
    NativeReset.runtimeBound overhead width firstCap 0 comparisonTime subtractTime +
    scalarComparisonTime + comparisonTime +
    6000 * overhead (256 * frameWidth width firstCap secondCap)


/-- Tape traversal uses entry width; retained configurations/results use full width. -/
def runtimeBoundWithTapeWidth (overhead : Nat → Nat)
    (width tapeWidth firstCap secondCap firstTime secondTime selectorTime sampleTime
      comparisonTime scalarComparisonTime subtractTime zeroTime : Nat) : Nat :=
  firstTime + secondTime + 2 * selectorTime + sampleTime +
    NativeLookup.runtimeBound overhead tapeWidth firstCap comparisonTime subtractTime zeroTime +
    NativeReset.runtimeBound overhead tapeWidth firstCap 0 comparisonTime subtractTime +
    scalarComparisonTime + comparisonTime +
    6000 * overhead (256 * frameWidth width firstCap secondCap)

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  {iface : Interface (C := C) unifSpec} {config out : Ty CryptoAtom}
  {select : out.Value (cryptoBase F G₁ G₂ K M) → Bool × Nat}
  (selector : Q.Realizer (rep.ty out) (rep.ty choiceTy) select)
  (pass : Code Q unifSpec iface (rep.ty (passInput config)) (rep.ty (passOutput out)))
  (sampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
  (mono : Monotone overhead)
  (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
  (routing : RoutingCostLaws control overhead)

include sizes lists laws dataLaws mono routing

theorem bound_with_tapeWidth
    (validConfig : config.Value (cryptoBase F G₁ G₂ K M) → Prop)
    (validOut : out.Value (cryptoBase F G₁ G₂ K M) → Prop)
    (width tapeWidth firstCap secondCap slotCap firstTime secondTime selectorTime sampleTime
      comparisonTime scalarComparisonTime subtractTime zeroTime : Nat)
    (htape : tapeWidth ≤ width)
    (hh : header ≤ tapeWidth) (hu : Q.size rep.data.unit () ≤ tapeWidth)
    (hb : ∀ b, Q.size rep.data.bool b ≤ tapeWidth) (hz : Q.size (rep.ty scalar) (0 : F) ≤ tapeWidth)
    (hn0 : Q.size rep.data.nat 0 ≤ tapeWidth) (hn1 : Q.size rep.data.nat 1 ≤ tapeWidth)
    (hn : ∀ n ≤ slotCap, Q.size rep.data.nat n ≤ tapeWidth)
    (hcompare : ∀ n m, Q.size rep.data.nat n ≤ tapeWidth → Q.size rep.data.nat m ≤ tapeWidth →
      (primitiveBound .natEq).time (n, m) ≤ comparisonTime)
    (hscalar : ∀ f g, Q.size (rep.ty scalar) f ≤ tapeWidth → Q.size (rep.ty scalar) g ≤ tapeWidth →
      (primitiveBound .scalarEq).time (f, g) ≤ scalarComparisonTime)
    (hsub : ∀ n ≤ slotCap, (primitiveBound .natSub).time (n, 1) ≤ subtractTime)
    (hzero : (primitiveBound .zero).time () ≤ zeroTime)
    (hinl : Q.cost (QS.inl rep.data.unit (rep.ty (.pair out out))) () ≤
      overhead (Q.size rep.data.unit () +
        Q.size (StepClass.HasSum.sum rep.data.unit (rep.ty (.pair out out))) (.inl ())))
    (hinr : ∀ p, Q.cost (QS.inr rep.data.unit (rep.ty (.pair out out))) p ≤
      overhead (Q.size (rep.ty (.pair out out)) p +
        Q.size (StepClass.HasSum.sum rep.data.unit (rep.ty (.pair out out))) (.inr p)))
    (hfirst : Bounds control queryCost pass
      (IncomingWidths (Q := Q) rep width tapeWidth 0 0 validConfig)
      (ReturnedWidths (Q := Q) rep width tapeWidth firstCap 0 validOut) firstTime)
    (hsecond : Bounds control queryCost pass
      (IncomingWidths (Q := Q) rep width tapeWidth (firstCap + 1) (firstCap + 1) validConfig)
      (ReturnedWidths (Q := Q) rep width tapeWidth secondCap (firstCap + 1) validOut) secondTime)
    (hselect : ∀ x, Ready (Q := Q) rep width validOut x → Q.cost selector x ≤ selectorTime)
    (hindex : ∀ x, Ready (Q := Q) rep width validOut x → (select x).2 ≤ slotCap)
    (hsample : Bounds control queryCost sampler (fun _ => True)
      (fun f => Q.size (rep.ty scalar) f ≤ tapeWidth) sampleTime) :
    Bounds control queryCost (code rep data cost primitive selector pass sampler)
      (Ready (Q := Q) rep width validConfig) (Result (Q := Q) rep width validOut)
      (runtimeBoundWithTapeWidth overhead width tapeWidth firstCap secondCap firstTime secondTime selectorTime sampleTime
        comparisonTime scalarComparisonTime subtractTime zeroTime) := by
  let cap := 16 * (firstCap + secondCap) + 64
  let W := cap * width
  let fee := overhead (256 * W)
  have hw : width ≤ W := by dsimp [W, cap]; nlinarith
  have htw : tapeWidth ≤ W := htape.trans hw
  let cfg := Frame.ready (Q := Q) rep config width validConfig
  let ret := Frame.ready (Q := Q) rep out width validOut
  let unitF : Frame (Q := Q) rep.data.unit width := ⟨fun _ => True, 1, fun _ _ => by simpa using hu.trans htape⟩
  let boolF : Frame (Q := Q) rep.data.bool width := ⟨fun _ => True, 1, fun b _ => by simpa using (hb b).trans htape⟩
  let fieldF : Frame (Q := Q) (rep.ty scalar) width :=
    ⟨fun f => Q.size (rep.ty scalar) f ≤ tapeWidth, 1, fun _ h => by simpa using h.trans htape⟩
  let slotF : Frame (Q := Q) rep.data.nat width :=
    ⟨fun n => n ≤ slotCap, 1, fun n h => by simpa using (hn n h).trans htape⟩
  let pair {A B : Type} {a : C.Str A} {b : C.Str B}
      (p : Frame (Q := Q) a width) (r : Frame (Q := Q) b width) := Frame.pair sizes p r (hh.trans htape)
  let sum {A B : Type} {a : C.Str A} {b : C.Str B}
      (p : Frame (Q := Q) a width) (r : Frame (Q := Q) b width) := Frame.sum sizes p r (hh.trans htape)
  let emptyState := Frame.stateAt rep sizes lists width tapeWidth 0 0 hh htape
  let firstState := Frame.stateAt rep sizes lists width tapeWidth firstCap 0 hh htape
  let resetState := Frame.stateAt rep sizes lists width tapeWidth (firstCap + 1) (firstCap + 1) hh htape
  let secondState := Frame.stateAt rep sizes lists width tapeWidth secondCap (firstCap + 1) hh htape
  let saved := Frame.tapeAt rep sizes lists width tapeWidth firstCap hh htape
  let choiceF := pair boolF slotF
  let firstInput := pair emptyState cfg
  let firstOutput := pair ret firstState
  let startF := pair firstInput cfg
  let firstF := pair firstOutput cfg
  let firstSelectionF := pair ret firstF
  let firstChoiceF := pair choiceF firstF
  let selectedF := pair slotF firstF
  let selectedBool := pair boolF selectedF
  let selectedSum := sum selectedF selectedF
  let freshRequest := pair unitF selectedF
  let freshF := pair fieldF selectedF
  let lookupInput := pair slotF saved
  let lookupOutput := pair boolF fieldF
  let lookupRequest := pair lookupInput freshF
  let collisionF := pair lookupOutput freshF
  let collisionBool := pair boolF freshF
  let collisionSum := sum freshF freshF
  let resetInput := pair slotF (pair fieldF firstState)
  let carryF := pair slotF (pair ret cfg)
  let resetRequest := pair resetInput carryF
  let afterReset := pair resetState carryF
  let secondInput := pair resetState cfg
  let secondCarryF := pair slotF ret
  let secondRequest := pair secondInput secondCarryF
  let secondOutput := pair ret secondState
  let secondF := pair secondOutput secondCarryF
  let secondSelectionF := pair ret secondF
  let secondChoiceF := pair choiceF secondF
  let pairOutput := pair ret ret
  let finishBool := pair boolF pairOutput
  let finishSum := sum pairOutput pairOutput
  let finalF := sum unitF pairOutput
  have cfgCap : cfg.factor ≤ cap := by
    dsimp only [
      cfg, pair, sum, Frame.pair, Frame.sum, Frame.ready, Frame.stateAt, Frame.tapeAt, cap]
    omega
  have retCap : ret.factor ≤ cap := by
    dsimp only [
      ret, pair, sum, Frame.pair, Frame.sum, Frame.ready, Frame.stateAt, Frame.tapeAt, cap]
    omega
  have unitFCap : unitF.factor ≤ cap := by
    dsimp only [
      unitF, pair, sum, Frame.pair, Frame.sum, Frame.ready, Frame.stateAt, Frame.tapeAt, cap]
    omega
  have boolFCap : boolF.factor ≤ cap := by
    dsimp only [
      boolF, pair, sum, Frame.pair, Frame.sum, Frame.ready, Frame.stateAt, Frame.tapeAt, cap]
    omega
  have fieldFCap : fieldF.factor ≤ cap := by
    dsimp only [
      fieldF, pair, sum, Frame.pair, Frame.sum, Frame.ready, Frame.stateAt, Frame.tapeAt, cap]
    omega
  have slotFCap : slotF.factor ≤ cap := by
    dsimp only [
      slotF, pair, sum, Frame.pair, Frame.sum, Frame.ready, Frame.stateAt, Frame.tapeAt, cap]
    omega
  have emptyStateCap : emptyState.factor ≤ cap := by
    dsimp only [
      emptyState, pair, sum, Frame.pair, Frame.sum, Frame.ready, Frame.stateAt, Frame.tapeAt, cap]
    omega
  have firstStateCap : firstState.factor ≤ cap := by
    dsimp only [
      firstState, pair, sum, Frame.pair, Frame.sum, Frame.ready, Frame.stateAt, Frame.tapeAt, cap]
    omega
  have resetStateCap : resetState.factor ≤ cap := by
    dsimp only [
      resetState, pair, sum, Frame.pair, Frame.sum, Frame.ready, Frame.stateAt, Frame.tapeAt, cap]
    omega
  have secondStateCap : secondState.factor ≤ cap := by
    dsimp only [
      secondState, pair, sum, Frame.pair, Frame.sum, Frame.ready, Frame.stateAt, Frame.tapeAt, cap]
    omega
  have savedCap : saved.factor ≤ cap := by
    dsimp only [
      saved, pair, sum, Frame.pair, Frame.sum, Frame.ready, Frame.stateAt, Frame.tapeAt, cap]
    omega
  have choiceFCap : choiceF.factor ≤ cap := by
    dsimp only [
      choiceF, boolF, slotF, pair, sum, Frame.pair, Frame.sum, Frame.ready, Frame.stateAt, Frame.tapeAt, cap]
    omega
  have firstInputCap : firstInput.factor ≤ cap := by
    dsimp only [
      firstInput, emptyState, cfg, pair, sum, Frame.pair, Frame.sum, Frame.ready, Frame.stateAt, Frame.tapeAt, cap]
    omega
  have firstOutputCap : firstOutput.factor ≤ cap := by
    dsimp only [
      firstOutput, ret, firstState, pair, sum, Frame.pair, Frame.sum, Frame.ready, Frame.stateAt, Frame.tapeAt,
      cap]
    omega
  have startFCap : startF.factor ≤ cap := by
    dsimp only [
      startF, firstInput, emptyState, cfg, pair, sum, Frame.pair, Frame.sum, Frame.ready,
      Frame.stateAt, Frame.tapeAt, cap]
    omega
  have firstFCap : firstF.factor ≤ cap := by
    dsimp only [
      firstF, firstOutput, ret, firstState, cfg, pair, sum, Frame.pair, Frame.sum, Frame.ready,
      Frame.stateAt, Frame.tapeAt, cap]
    omega
  have firstSelectionFCap : firstSelectionF.factor ≤ cap := by
    dsimp only [
      firstSelectionF, ret, firstF, firstOutput, firstState, cfg, pair, sum, Frame.pair,
      Frame.sum, Frame.ready, Frame.stateAt, Frame.tapeAt, cap]
    omega
  have firstChoiceFCap : firstChoiceF.factor ≤ cap := by
    dsimp only [
      firstChoiceF, choiceF, boolF, slotF, firstF, firstOutput, ret, firstState, cfg, pair, sum,
      Frame.pair, Frame.sum, Frame.ready, Frame.stateAt, Frame.tapeAt, cap]
    omega
  have selectedFCap : selectedF.factor ≤ cap := by
    dsimp only [
      selectedF, slotF, firstF, firstOutput, ret, firstState, cfg, pair, sum, Frame.pair,
      Frame.sum, Frame.ready, Frame.stateAt, Frame.tapeAt, cap]
    omega
  have selectedBoolCap : selectedBool.factor ≤ cap := by
    dsimp only [
      selectedBool, boolF, selectedF, slotF, firstF, firstOutput, ret, firstState, cfg, pair, sum,
      Frame.pair, Frame.sum, Frame.ready, Frame.stateAt, Frame.tapeAt, cap]
    omega
  have selectedSumCap : selectedSum.factor ≤ cap := by
    dsimp only [
      selectedSum, selectedF, slotF, firstF, firstOutput, ret, firstState, cfg, pair, sum,
      Frame.pair, Frame.sum, Frame.ready, Frame.stateAt, Frame.tapeAt, cap]
    omega
  have freshRequestCap : freshRequest.factor ≤ cap := by
    dsimp only [
      freshRequest, unitF, selectedF, slotF, firstF, firstOutput, ret, firstState, cfg, pair, sum,
      Frame.pair, Frame.sum, Frame.ready, Frame.stateAt, Frame.tapeAt, cap]
    omega
  have freshFCap : freshF.factor ≤ cap := by
    dsimp only [
      freshF, fieldF, selectedF, slotF, firstF, firstOutput, ret, firstState, cfg, pair, sum,
      Frame.pair, Frame.sum, Frame.ready, Frame.stateAt, Frame.tapeAt, cap]
    omega
  have lookupInputCap : lookupInput.factor ≤ cap := by
    dsimp only [
      lookupInput, slotF, saved, pair, sum, Frame.pair, Frame.sum, Frame.ready, Frame.stateAt, Frame.tapeAt, cap]
    omega
  have lookupOutputCap : lookupOutput.factor ≤ cap := by
    dsimp only [
      lookupOutput, boolF, fieldF, pair, sum, Frame.pair, Frame.sum, Frame.ready, Frame.stateAt, Frame.tapeAt, cap]
    omega
  have lookupRequestCap : lookupRequest.factor ≤ cap := by
    dsimp only [
      lookupRequest, lookupInput, slotF, saved, freshF, fieldF, selectedF, firstF, firstOutput,
      ret, firstState, cfg, pair, sum, Frame.pair, Frame.sum, Frame.ready, Frame.stateAt, Frame.tapeAt, cap]
    omega
  have collisionFCap : collisionF.factor ≤ cap := by
    dsimp only [
      collisionF, lookupOutput, boolF, fieldF, freshF, selectedF, slotF, firstF, firstOutput, ret,
      firstState, cfg, pair, sum, Frame.pair, Frame.sum, Frame.ready, Frame.stateAt, Frame.tapeAt, cap]
    omega
  have collisionBoolCap : collisionBool.factor ≤ cap := by
    dsimp only [
      collisionBool, boolF, freshF, fieldF, selectedF, slotF, firstF, firstOutput, ret,
      firstState, cfg, pair, sum, Frame.pair, Frame.sum, Frame.ready, Frame.stateAt, Frame.tapeAt, cap]
    omega
  have collisionSumCap : collisionSum.factor ≤ cap := by
    dsimp only [
      collisionSum, freshF, fieldF, selectedF, slotF, firstF, firstOutput, ret, firstState, cfg,
      pair, sum, Frame.pair, Frame.sum, Frame.ready, Frame.stateAt, Frame.tapeAt, cap]
    omega
  have resetInputCap : resetInput.factor ≤ cap := by
    dsimp only [
      resetInput, slotF, fieldF, firstState, pair, sum, Frame.pair, Frame.sum, Frame.ready,
      Frame.stateAt, Frame.tapeAt, cap]
    omega
  have carryFCap : carryF.factor ≤ cap := by
    dsimp only [
      carryF, slotF, ret, cfg, pair, sum, Frame.pair, Frame.sum, Frame.ready, Frame.stateAt, Frame.tapeAt, cap]
    omega
  have resetRequestCap : resetRequest.factor ≤ cap := by
    dsimp only [
      resetRequest, resetInput, slotF, fieldF, firstState, carryF, ret, cfg, pair, sum,
      Frame.pair, Frame.sum, Frame.ready, Frame.stateAt, Frame.tapeAt, cap]
    omega
  have afterResetCap : afterReset.factor ≤ cap := by
    dsimp only [
      afterReset, resetState, carryF, slotF, ret, cfg, pair, sum, Frame.pair, Frame.sum,
      Frame.ready, Frame.stateAt, Frame.tapeAt, cap]
    omega
  have secondInputCap : secondInput.factor ≤ cap := by
    dsimp only [
      secondInput, resetState, cfg, pair, sum, Frame.pair, Frame.sum, Frame.ready, Frame.stateAt, Frame.tapeAt,
      cap]
    omega
  have secondCarryFCap : secondCarryF.factor ≤ cap := by
    dsimp only [
      secondCarryF, slotF, ret, pair, sum, Frame.pair, Frame.sum, Frame.ready, Frame.stateAt, Frame.tapeAt, cap]
    omega
  have secondRequestCap : secondRequest.factor ≤ cap := by
    dsimp only [
      secondRequest, secondInput, resetState, cfg, secondCarryF, slotF, ret, pair, sum,
      Frame.pair, Frame.sum, Frame.ready, Frame.stateAt, Frame.tapeAt, cap]
    omega
  have secondOutputCap : secondOutput.factor ≤ cap := by
    dsimp only [
      secondOutput, ret, secondState, pair, sum, Frame.pair, Frame.sum, Frame.ready, Frame.stateAt, Frame.tapeAt,
      cap]
    omega
  have secondFCap : secondF.factor ≤ cap := by
    dsimp only [
      secondF, secondOutput, ret, secondState, secondCarryF, slotF, pair, sum, Frame.pair,
      Frame.sum, Frame.ready, Frame.stateAt, Frame.tapeAt, cap]
    omega
  have secondSelectionFCap : secondSelectionF.factor ≤ cap := by
    dsimp only [
      secondSelectionF, ret, secondF, secondOutput, secondState, secondCarryF, slotF, pair, sum,
      Frame.pair, Frame.sum, Frame.ready, Frame.stateAt, Frame.tapeAt, cap]
    omega
  have secondChoiceFCap : secondChoiceF.factor ≤ cap := by
    dsimp only [
      secondChoiceF, choiceF, boolF, slotF, secondF, secondOutput, ret, secondState, secondCarryF,
      pair, sum, Frame.pair, Frame.sum, Frame.ready, Frame.stateAt, Frame.tapeAt, cap]
    omega
  have pairOutputCap : pairOutput.factor ≤ cap := by
    dsimp only [
      pairOutput, ret, pair, sum, Frame.pair, Frame.sum, Frame.ready, Frame.stateAt, Frame.tapeAt, cap]
    omega
  have finishBoolCap : finishBool.factor ≤ cap := by
    dsimp only [
      finishBool, boolF, pairOutput, ret, pair, sum, Frame.pair, Frame.sum, Frame.ready,
      Frame.stateAt, Frame.tapeAt, cap]
    omega
  have finishSumCap : finishSum.factor ≤ cap := by
    dsimp only [
      finishSum, pairOutput, ret, pair, sum, Frame.pair, Frame.sum, Frame.ready, Frame.stateAt, Frame.tapeAt, cap]
    omega
  have finalFCap : finalF.factor ≤ cap := by
    dsimp only [
      finalF, unitF, pairOutput, ret, pair, sum, Frame.pair, Frame.sum, Frame.ready, Frame.stateAt, Frame.tapeAt,
      cap]
    omega
  have sized {A : Type} {a : C.Str A} (p : Frame (Q := Q) a width) (hc : p.factor ≤ cap)
      (x : A) (hp : p.property x) : Q.size a x ≤ W :=
    (p.size_le x hp).trans (Nat.mul_le_mul_right width hc)
  have emptyValid : emptyState.property ([], []) := by
    simp [emptyState, Frame.stateAt, NativeUniform.StateBound, NativeUniform.TapeBound]
  have selectorBound := Frame.atomic (iface := iface) mono control queryCost routing selector ret choiceF selectorTime
    retCap choiceFCap (fun x hx => And.intro trivial (hindex x hx)) hselect
  have firstBound := Frame.first mono control queryCost routing firstInput firstOutput cfg
    cfgCap firstOutputCap hfirst
  have secondPassBound := Frame.first mono control queryCost routing secondInput secondOutput secondCarryF
    secondCarryFCap secondOutputCap hsecond
  have firstSelectorBound := Frame.first mono control queryCost routing ret choiceF firstF
    firstFCap choiceFCap selectorBound
  have secondSelectorBound := Frame.first mono control queryCost routing ret choiceF secondF
    secondFCap choiceFCap selectorBound
  have sampleBound := Frame.first mono control queryCost routing unitF fieldF selectedF
    selectedFCap fieldFCap hsample
  have lookupCoreBound : Bounds control queryCost (NativeLookup.code rep data cost primitive (iface := iface))
      lookupInput.property lookupOutput.property
      (NativeLookup.runtimeBound overhead tapeWidth firstCap comparisonTime subtractTime zeroTime) := by
    intro input hi z hz'
    obtain ⟨ho, ht⟩ := NativeLookup.bound rep sizes lists data cost primitive laws dataLaws primitiveBound
      mono control queryCost routing tapeWidth firstCap slotCap comparisonTime subtractTime zeroTime
      hh hu hb hz hn0 hn1 hn hcompare hsub hzero input hi z hz'
    exact ⟨⟨trivial, ho⟩, ht⟩
  have lookupRetained := Frame.first mono control queryCost routing lookupInput lookupOutput freshF
    freshFCap lookupOutputCap lookupCoreBound
  have resetCoreBound := NativeReset.bound rep data cost primitive sizes lists laws dataLaws primitiveBound
    mono control queryCost routing (iface := iface) tapeWidth firstCap 0 slotCap comparisonTime subtractTime
    hh hu hb hn0 hn1 hn hcompare hsub
  have resetRetained := Frame.first mono control queryCost routing resetInput resetState carryF
    carryFCap resetStateCap resetCoreBound
  have startBound := Frame.atomic (iface := iface) mono control queryCost routing
    (compileLocal rep data cost primitive (startExpression config)) cfg startF (516 * fee)
    cfgCap startFCap (fun x hx => ⟨⟨emptyValid, hx⟩, hx⟩)
    (fun x hx => start_cost rep data cost primitive sizes lists laws dataLaws mono
      x W (hh.trans htw) (hu.trans htw) (sized cfg cfgCap x hx))
  have firstSelectionBound := Frame.atomic (iface := iface) mono control queryCost routing
    (compileLocal rep data cost primitive (firstSelectionExpression config out)) firstF firstSelectionF (516 * fee)
    firstFCap firstSelectionFCap (fun x hx => ⟨hx.1.1, hx⟩)
    (fun x hx => firstSelection_cost rep data cost primitive sizes laws dataLaws mono
      x W (hh.trans htw) (hu.trans htw) (sized firstF firstFCap x hx))
  have freshBound := Frame.atomic (iface := iface) mono control queryCost routing
    (compileLocal rep data cost primitive (freshExpression config out)) selectedF freshRequest (516 * fee)
    selectedFCap freshRequestCap (fun x hx => ⟨trivial, hx⟩)
    (fun x hx => fresh_cost rep data cost primitive sizes laws dataLaws mono
      x W (hh.trans htw) (hu.trans htw) (sized selectedF selectedFCap x hx))
  have lookupBound := Frame.atomic (iface := iface) mono control queryCost routing
    (compileLocal rep data cost primitive (lookupExpression config out)) freshF lookupRequest (516 * fee)
    freshFCap lookupRequestCap (fun x hx => ⟨⟨hx.2.1, hx.2.2.1.2.1⟩, hx⟩)
    (fun x hx => lookup_cost rep data cost primitive sizes laws dataLaws mono
      x W (hh.trans htw) (hu.trans htw) (sized freshF freshFCap x hx))
  have resetBound := Frame.atomic (iface := iface) mono control queryCost routing
    (compileLocal rep data cost primitive (resetExpression config out)) freshF resetRequest (516 * fee)
    freshFCap resetRequestCap (fun x hx => ⟨⟨hx.2.1, hx.1, hx.2.2.1.2⟩, hx.2.1, hx.2.2.1.1, hx.2.2.2⟩)
    (fun x hx => reset_cost rep data cost primitive sizes laws dataLaws mono
      x W (hh.trans htw) (hu.trans htw) (sized freshF freshFCap x hx))
  have secondBound := Frame.atomic (iface := iface) mono control queryCost routing
    (compileLocal rep data cost primitive (secondExpression config out)) afterReset secondRequest (516 * fee)
    afterResetCap secondRequestCap (fun x hx => ⟨⟨hx.1, hx.2.2.2⟩, hx.2.1, hx.2.2.1⟩)
    (fun x hx => second_cost rep data cost primitive sizes laws dataLaws mono
      x W (hh.trans htw) (hu.trans htw) (sized afterReset afterResetCap x hx))
  have secondSelectionBound := Frame.atomic (iface := iface) mono control queryCost routing
    (compileLocal rep data cost primitive (secondSelectionExpression out)) secondF secondSelectionF (516 * fee)
    secondFCap secondSelectionFCap (fun x hx => ⟨hx.1.1, hx⟩)
    (fun x hx => secondSelection_cost rep data cost primitive sizes laws dataLaws mono
      x W (hh.trans htw) (hu.trans htw) (sized secondF secondFCap x hx))
  have firstChoiceProperty (x : _) (hx : firstChoiceF.property x) :
      selectedBool.property ((firstChoiceExpression config out).denote (arithmetic F G₁ G₂ K M cost) (x, ())) :=
    ⟨trivial, ⟨hx.1.2, hx.2⟩⟩
  have firstChoiceBound := Frame.atomic (iface := iface) mono control queryCost routing
    (chooseLocal rep data cost primitive (firstChoiceExpression config out)) firstChoiceF selectedSum (0 + 518 * fee)
    firstChoiceFCap selectedSumCap (by
      intro x hx
      change Sum.elim selectedF.property selectedF.property (if _ then _ else _)
      split <;> exact (firstChoiceProperty x hx).2) (by
      intro x hx
      have hc := firstChoice_cost rep data cost primitive sizes laws dataLaws mono
        x W (hh.trans htw) (hu.trans htw) (sized firstChoiceF firstChoiceFCap x hx)
      exact (chooseLocal_cost rep data cost primitive sizes laws dataLaws mono
        (firstChoiceExpression config out) x W (0 + 516 * fee) (hh.trans htw)
        (sized firstChoiceF firstChoiceFCap x hx)
        (sized selectedBool selectedBoolCap _ (firstChoiceProperty x hx)) (by simpa only [Nat.zero_add] using hc)).trans
          (by dsimp only [fee]; omega))
  have collisionProperty (x : _) (hx : collisionF.property x) :
      collisionBool.property ((collisionExpression config out).denote (arithmetic F G₁ G₂ K M cost) (x, ())) :=
    ⟨trivial, hx.2⟩
  have collisionBound := Frame.atomic (iface := iface) mono control queryCost routing
    (chooseLocal rep data cost primitive (collisionExpression config out)) collisionF collisionSum (scalarComparisonTime + 518 * fee)
    collisionFCap collisionSumCap (by
      intro x hx
      change Sum.elim freshF.property freshF.property (if _ then _ else _)
      split <;> exact (collisionProperty x hx).2) (by
      intro x hx
      have hc := collision_cost rep data cost primitive sizes laws dataLaws primitiveBound mono
        x W scalarComparisonTime (hh.trans htw) (hu.trans htw) (fun b => (hb b).trans htw)
        (sized collisionF collisionFCap x hx) (hscalar x.1.2 x.2.1 hx.1.2 hx.2.1)
      exact (chooseLocal_cost rep data cost primitive sizes laws dataLaws mono
        (collisionExpression config out) x W (scalarComparisonTime + 516 * fee) (hh.trans htw)
        (sized collisionF collisionFCap x hx)
        (sized collisionBool collisionBoolCap _ (collisionProperty x hx)) (by simpa only [Nat.zero_add] using hc)).trans
          (by dsimp only [fee]; omega))
  have finishProperty (x : _) (hx : secondChoiceF.property x) :
      finishBool.property ((finishExpression out).denote (arithmetic F G₁ G₂ K M cost) (x, ())) :=
    ⟨trivial, ⟨hx.2.2.2, hx.2.1.1⟩⟩
  have finishBound := Frame.atomic (iface := iface) mono control queryCost routing
    (chooseLocal rep data cost primitive (finishExpression out)) secondChoiceF finishSum (comparisonTime + 518 * fee)
    secondChoiceFCap finishSumCap (by
      intro x hx
      change Sum.elim pairOutput.property pairOutput.property (if _ then _ else _)
      split <;> exact (finishProperty x hx).2) (by
      intro x hx
      have hc := finish_cost rep data cost primitive sizes laws dataLaws primitiveBound mono
        x W comparisonTime (hh.trans htw) (hu.trans htw) (fun b => (hb b).trans htw)
        (sized secondChoiceF secondChoiceFCap x hx) (hcompare x.1.2 x.2.2.1 (hn _ hx.1.2) (hn _ hx.2.2.1))
      exact (chooseLocal_cost rep data cost primitive sizes laws dataLaws mono
        (finishExpression out) x W (comparisonTime + 516 * fee) (hh.trans htw)
        (sized secondChoiceF secondChoiceFCap x hx)
        (sized finishBool finishBoolCap _ (finishProperty x hx)) (by simpa only [Nat.zero_add] using hc)).trans
          (by dsimp only [fee]; omega))
  have rejectBound (input : Ty CryptoAtom) (pre : Frame (Q := Q) (rep.ty input) width)
      (hcap : pre.factor ≤ cap) :
      Bounds control queryCost (.atomic (iface := iface) (reject rep data input out))
        pre.property finalF.property (4 * fee) := by
    have h := Frame.atomic (iface := iface) mono control queryCost routing (reject rep data input out)
      pre finalF (3 * fee) hcap finalFCap (fun _ _ => trivial)
      (fun x hx => reject_cost rep data sizes laws dataLaws mono input out x W
        (hh.trans htw) (hu.trans htw) (sized pre hcap x hx) hinl)
    exact Frame.widen control queryCost h (by dsimp only [fee, W]; omega)
  have acceptBound : Bounds control queryCost
      (.atomic (iface := iface) (QS.inr rep.data.unit (rep.ty (.pair out out))))
      pairOutput.property finalF.property (2 * fee) := by
    have h := Frame.atomic (iface := iface) mono control queryCost routing (QS.inr rep.data.unit (rep.ty (.pair out out)))
      pairOutput finalF fee pairOutputCap finalFCap (fun _ hx => hx) (by
        intro x hx
        have hi := sized pairOutput pairOutputCap x hx
        have ho := sized finalF finalFCap (.inr x) hx
        change Q.size (rep.ty (.pair out out)) x ≤ W at hi
        change Q.size (StepClass.HasSum.sum rep.data.unit (rep.ty (.pair out out))) (.inr x) ≤ W at ho
        exact (hinr x).trans (mono (by change _ ≤ 256 * W; omega)))
    exact Frame.widen control queryCost h (by dsimp only [fee, W]; omega)
  have finishBranch := Frame.branch mono control queryCost routing pairOutput pairOutput finishSum finalF
    rfl finishSumCap acceptBound (rejectBound (.pair out out) pairOutput pairOutputCap)
  have replay6 := Frame.seq mono control queryCost routing secondChoiceF finishSum finalF
    secondChoiceFCap finishSumCap finishBound finishBranch
  have replay5 := Frame.seq mono control queryCost routing secondSelectionF secondChoiceF finalF
    secondSelectionFCap secondChoiceFCap secondSelectorBound replay6
  have replay4 := Frame.seq mono control queryCost routing secondF secondSelectionF finalF
    secondFCap secondSelectionFCap secondSelectionBound replay5
  have replay3 := Frame.seq mono control queryCost routing secondRequest secondF finalF
    secondRequestCap secondFCap secondPassBound replay4
  have replay2 := Frame.seq mono control queryCost routing afterReset secondRequest finalF
    afterResetCap secondRequestCap secondBound replay3
  have replay1 := Frame.seq mono control queryCost routing resetRequest afterReset finalF
    resetRequestCap afterResetCap resetRetained replay2
  have replay0 := Frame.seq mono control queryCost routing freshF resetRequest finalF
    freshFCap resetRequestCap resetBound replay1
  have collisionBranch := Frame.branch mono control queryCost routing freshF freshF collisionSum finalF
    rfl collisionSumCap (rejectBound (freshTy config out) freshF freshFCap) replay0
  have selected4 := Frame.seq mono control queryCost routing collisionF collisionSum finalF
    collisionFCap collisionSumCap collisionBound collisionBranch
  have selected3 := Frame.seq mono control queryCost routing lookupRequest collisionF finalF
    lookupRequestCap collisionFCap lookupRetained selected4
  have selected2 := Frame.seq mono control queryCost routing freshF lookupRequest finalF
    freshFCap lookupRequestCap lookupBound selected3
  have selected1 := Frame.seq mono control queryCost routing freshRequest freshF finalF
    freshRequestCap freshFCap sampleBound selected2
  have selected0 := Frame.seq mono control queryCost routing selectedF freshRequest finalF
    selectedFCap freshRequestCap freshBound selected1
  have firstBranch := Frame.branch mono control queryCost routing selectedF selectedF selectedSum finalF
    rfl selectedSumCap selected0 (rejectBound (selectedTy config out) selectedF selectedFCap)
  have controller4 := Frame.seq mono control queryCost routing firstChoiceF selectedSum finalF
    firstChoiceFCap selectedSumCap firstChoiceBound firstBranch
  have controller3 := Frame.seq mono control queryCost routing firstSelectionF firstChoiceF finalF
    firstSelectionFCap firstChoiceFCap firstSelectorBound controller4
  have controller2 := Frame.seq mono control queryCost routing firstF firstSelectionF finalF
    firstFCap firstSelectionFCap firstSelectionBound controller3
  have controller1 := Frame.seq mono control queryCost routing startF firstF finalF
    startFCap firstFCap firstBound controller2
  have controller0 := Frame.seq mono control queryCost routing cfg startF finalF
    cfgCap startFCap startBound controller1
  exact Frame.widen control queryCost controller0 (by
    dsimp only [runtimeBoundWithTapeWidth, frameWidth, fee, W, cap]
    omega)

/-- Equal-width specialization retained for existing controller users. -/
theorem bound
    (validConfig : config.Value (cryptoBase F G₁ G₂ K M) → Prop)
    (validOut : out.Value (cryptoBase F G₁ G₂ K M) → Prop)
    (width firstCap secondCap slotCap firstTime secondTime selectorTime sampleTime
      comparisonTime scalarComparisonTime subtractTime zeroTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width) (hz : Q.size (rep.ty scalar) (0 : F) ≤ width)
    (hn0 : Q.size rep.data.nat 0 ≤ width) (hn1 : Q.size rep.data.nat 1 ≤ width)
    (hn : ∀ n ≤ slotCap, Q.size rep.data.nat n ≤ width)
    (hcompare : ∀ n m, Q.size rep.data.nat n ≤ width → Q.size rep.data.nat m ≤ width →
      (primitiveBound .natEq).time (n, m) ≤ comparisonTime)
    (hscalar : ∀ f g, Q.size (rep.ty scalar) f ≤ width → Q.size (rep.ty scalar) g ≤ width →
      (primitiveBound .scalarEq).time (f, g) ≤ scalarComparisonTime)
    (hsub : ∀ n ≤ slotCap, (primitiveBound .natSub).time (n, 1) ≤ subtractTime)
    (hzero : (primitiveBound .zero).time () ≤ zeroTime)
    (hinl : Q.cost (QS.inl rep.data.unit (rep.ty (.pair out out))) () ≤
      overhead (Q.size rep.data.unit () +
        Q.size (StepClass.HasSum.sum rep.data.unit (rep.ty (.pair out out))) (.inl ())))
    (hinr : ∀ p, Q.cost (QS.inr rep.data.unit (rep.ty (.pair out out))) p ≤
      overhead (Q.size (rep.ty (.pair out out)) p +
        Q.size (StepClass.HasSum.sum rep.data.unit (rep.ty (.pair out out))) (.inr p)))
    (hfirst : Bounds control queryCost pass
      (Incoming (Q := Q) rep width 0 0 validConfig)
      (Returned (Q := Q) rep width firstCap 0 validOut) firstTime)
    (hsecond : Bounds control queryCost pass
      (Incoming (Q := Q) rep width (firstCap + 1) (firstCap + 1) validConfig)
      (Returned (Q := Q) rep width secondCap (firstCap + 1) validOut) secondTime)
    (hselect : ∀ x, Ready (Q := Q) rep width validOut x → Q.cost selector x ≤ selectorTime)
    (hindex : ∀ x, Ready (Q := Q) rep width validOut x → (select x).2 ≤ slotCap)
    (hsample : Bounds control queryCost sampler (fun _ => True)
      (fun f => Q.size (rep.ty scalar) f ≤ width) sampleTime) :
    Bounds control queryCost (code rep data cost primitive selector pass sampler)
      (Ready (Q := Q) rep width validConfig) (Result (Q := Q) rep width validOut)
      (runtimeBound overhead width firstCap secondCap firstTime secondTime selectorTime sampleTime
        comparisonTime scalarComparisonTime subtractTime zeroTime) := by
  exact bound_with_tapeWidth rep data cost primitive selector pass sampler sizes lists laws dataLaws
    primitiveBound mono control queryCost routing validConfig validOut
    width width firstCap secondCap slotCap firstTime secondTime selectorTime sampleTime
    comparisonTime scalarComparisonTime subtractTime zeroTime le_rfl hh hu hb hz hn0 hn1 hn
    hcompare hscalar hsub hzero hinl hinr hfirst hsecond hselect hindex hsample

omit sizes lists laws dataLaws mono routing in
theorem runtimeBoundWithTapeWidth_polynomial (overhead : Nat → Nat → Nat)
    (width tapeWidth firstCap secondCap firstTime secondTime selectorTime sampleTime
      comparisonTime scalarComparisonTime subtractTime zeroTime : Nat → Nat)
    (hOverhead : PolynomialOverhead overhead) (hWidth : PolynomiallyBounded width)
    (hTape : PolynomiallyBounded tapeWidth)
    (hFirstCap : PolynomiallyBounded firstCap) (hSecondCap : PolynomiallyBounded secondCap)
    (hFirst : PolynomiallyBounded firstTime) (hSecond : PolynomiallyBounded secondTime)
    (hSelector : PolynomiallyBounded selectorTime) (hSample : PolynomiallyBounded sampleTime)
    (hCompare : PolynomiallyBounded comparisonTime) (hScalar : PolynomiallyBounded scalarComparisonTime)
    (hSubtract : PolynomiallyBounded subtractTime) (hZero : PolynomiallyBounded zeroTime) :
    PolynomiallyBounded (fun n => runtimeBoundWithTapeWidth (overhead n) (width n) (tapeWidth n)
      (firstCap n) (secondCap n) (firstTime n) (secondTime n) (selectorTime n) (sampleTime n)
      (comparisonTime n) (scalarComparisonTime n) (subtractTime n) (zeroTime n)) := by
  unfold runtimeBoundWithTapeWidth frameWidth
  repeat' first
    | assumption
    | apply NativeLookup.runtimeBound_polynomial
    | apply NativeReset.runtimeBound_polynomial
    | apply PolynomiallyBounded.add
    | apply PolynomiallyBounded.mul
    | apply hOverhead.apply
    | apply PolynomiallyBounded.const

omit sizes lists laws dataLaws mono routing in
theorem runtimeBound_polynomial (overhead : Nat → Nat → Nat)
    (width firstCap secondCap firstTime secondTime selectorTime sampleTime
      comparisonTime scalarComparisonTime subtractTime zeroTime : Nat → Nat)
    (hOverhead : PolynomialOverhead overhead) (hWidth : PolynomiallyBounded width)
    (hFirstCap : PolynomiallyBounded firstCap) (hSecondCap : PolynomiallyBounded secondCap)
    (hFirst : PolynomiallyBounded firstTime) (hSecond : PolynomiallyBounded secondTime)
    (hSelector : PolynomiallyBounded selectorTime) (hSample : PolynomiallyBounded sampleTime)
    (hCompare : PolynomiallyBounded comparisonTime) (hScalar : PolynomiallyBounded scalarComparisonTime)
    (hSubtract : PolynomiallyBounded subtractTime) (hZero : PolynomiallyBounded zeroTime) :
    PolynomiallyBounded (fun n => runtimeBound (overhead n) (width n) (firstCap n) (secondCap n)
      (firstTime n) (secondTime n) (selectorTime n) (sampleTime n)
      (comparisonTime n) (scalarComparisonTime n) (subtractTime n) (zeroTime n)) := by
  unfold runtimeBound frameWidth
  repeat' first
    | assumption
    | apply NativeLookup.runtimeBound_polynomial
    | apply NativeReset.runtimeBound_polynomial
    | apply PolynomiallyBounded.add
    | apply PolynomiallyBounded.mul
    | apply hOverhead.apply
    | apply PolynomiallyBounded.const

end Signatures.Runtime.Schnorr.RawTape.NativeFork
