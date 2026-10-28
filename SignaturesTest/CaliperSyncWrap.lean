import Proofs.Runtime.Caliper.SyncWrapCaller
import Proofs.Runtime.Caliper.SyncWrapFinishBounds
import Proofs.Runtime.Caliper.SyncTerms
import Proofs.Runtime.Caliper.BLSExtractArithmeticNames
import Proofs.Runtime.Caliper.BLSResponseNames
import Mathlib.Data.BitVec
import Lean

/-! Execute the synchronized PS wrapper around a trivial inner caller on 64-bit words. Word
arithmetic exercises the code paths (forwarding, hash before signing, corrected reply, final
hash, finish), not a field security model. -/
namespace SignaturesTest.CaliperSyncWrap
open Caliper OracleComp OracleSpec Signatures.Runtime Signatures.Runtime.CaliperBackend BoundedSource WeightedFull
open Signatures.Runtime.CaliperBackend.SyncWrap

private def scalar : Layout 64 (Word 64) := Layout.all (wordRepresentation 64 (by decide))
private abbrev Key := Word 64
private def base : Bool → Type
  | false => Key
  | true => Word 64
private instance : DecidableEq (Ty.Value base (.atom false)) := inferInstanceAs (DecidableEq Key)
private instance (n : Nat) : OfNat (Ty.Value base (.atom true)) n := inferInstanceAs (OfNat (Word 64) n)
private instance (n : Nat) : OfNat (Ty.Value base (.atom false)) n := inferInstanceAs (OfNat (Word 64) n)
private instance : Zero (Ty.Value base (.atom true)) := inferInstanceAs (Zero (Word 64))

private def accumulation : BLSPrivateAccumulate.Layouts 64 Key (Word 64) where
  cache := {
    key := scalar
    value := scalar
    capacityPred := 15
    wordFits := by decide
    countFits := by decide
    storageFits := by decide }
  pairStorageFits := by decide
  scalarStorageFits := by decide
  goodStorageFits := by decide
  badStorageFits := by decide

/-- Messages are period/scalar rows. -/
private def message : Layout 64 (Key × Word 64) := WeightedRows.term accumulation.good

private def rows : SharedRows 64 Key (Key × Word 64) (Word 64) (Word 64) where
  accumulation := accumulation
  message := message
  point := scalar
  goodWeightedFits := by decide
  badWeightedFits := by decide
  goodRowsFits := by decide
  badRowsFits := by decide
  responseFits := by decide

private def scheme : SharedScheme 64 Key (Key × Word 64) (Word 64) (Word 64) where
  rows := rows
  signs := 6
  xi := 6
  terms := 1
  hashes := 6
  gamma := 6
  goodBounds := ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
  badBounds := ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
  zeroValid := trivial
  hashPositive := by decide
  signPositive := by decide
  goodServiceFits := by decide
  badServiceFits := by decide

private def inner : SharedLayouts 64 Key (Key × Word 64) (Word 64) (Word 64) (Word 64 × Word 64)
    scheme.goodBounds.extraction.forgery.Value where
  scheme := scheme
  key := scalar.prod scalar (by decide)
  state := scheme.goodBounds.extraction.forgery.representation
  randomBound := 18446744073709551615
  randomFits := by decide
  goodCallerFits := by decide
  badCallerFits := by decide
  goodSetupFits := by decide
  badSetupFits := by decide
  samplingFits := by decide

/-- The wrapper's core, typed at the `Ty` encoding so the wrapper's routines apply directly. -/
private def core : Core 64 (Ty.Value base (.atom false)) (Ty.Value base (.atom false) × Ty.Value base (.atom true)) (Word 64)
    (Ty.Value base (.atom true)) (Word 64 × Word 64) scheme.goodBounds.extraction.forgery.Value :=
  ⟨inner, 8, 64, by decide⟩

private def caps : Capacities core.inner.scheme where
  hashes := 8
  gammaPred := 8
  goodBounds := ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
  badBounds := ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
  hashPositive := by decide
  goodServiceFits := by decide
  badServiceFits := by decide

private def wrapper : Wrapper core where
  caps := caps
  goodCallerFits := by decide
  badCallerFits := by decide
  goodSetupFits := by decide
  badSetupFits := by decide
  samplingFits := by decide
  gammaRoom := by decide

private theorem outLe : wrapper.outer.good.forgery.representation.encoding.words ≤ core.outWords := by decide

/-! ## Word arithmetic -/

/-- A scalar value is a word with the trivial certificate. -/
private abbrev word (x : Word 64) : core.scalar.Value := ⟨x, trivial⟩

private def binary (op : BinOp) : Implementation .unit (core.scalarAll.prod core.scalarAll (by decide)) core.scalarAll
    (fun value => word (op.eval value.1.val value.2.val)) where
  preserves _ _ := trivial
  program := ((WordBinary.realizer .unit op (by decide)).viewInput (core.scalarAll.prod core.scalarAll (by decide)).representation
    (fun value => (value.val.1.val, value.val.2.val)) (fun _ => rfl)).viewOutput core.scalarAll.representation
      (fun value => ⟨word (op.eval value.val.1.val value.val.2.val), trivial⟩) (fun _ => rfl)
private def mulAll := binary .mul
private def addAll := binary .add
private theorem mulAllBound : mulAll.BoundedBy 6 27 := ⟨fun _ => le_rfl, by decide⟩
private theorem addAllBound : addAll.BoundedBy 6 27 := ⟨fun _ => le_rfl, by decide⟩
private theorem mulAllNames : NamesBound mulAll.program.code 3 := ⟨by decide, by decide⟩
private theorem addAllNames : NamesBound addAll.program.code 3 := ⟨by decide, by decide⟩

/-- The same operations at the finish's unwrapped scalar layout. -/
private def binary' (op : BinOp) : Implementation .unit (core.scalar.prod core.scalar (by decide)) core.scalar
    (fun value => op.eval value.1 value.2) where
  preserves _ _ := trivial
  program := ((WordBinary.realizer .unit op (by decide)).viewInput (core.scalar.prod core.scalar (by decide)).representation
    (fun value => value.val) (fun _ => rfl)).viewOutput core.scalar.representation
      (fun value => ⟨op.eval value.val.1 value.val.2, trivial⟩) (fun _ => rfl)
private def mul' := binary' .mul
private def sub' := binary' .sub
private theorem mul'Bound : mul'.BoundedBy 6 27 := ⟨fun _ => le_rfl, by decide⟩
private theorem sub'Bound : sub'.BoundedBy 6 27 := ⟨fun _ => le_rfl, by decide⟩
private theorem mul'Names : NamesBound mul'.program.code 3 := ⟨by decide, by decide⟩
private theorem sub'Names : NamesBound sub'.program.code 3 := ⟨by decide, by decide⟩

/-! ## The wrapper's routines: hash of the period, correction `k · m`, fused multiply-add -/

private def hashOf : Implementation .unit core.messageAll core.keyAll (fun m => ⟨m.val.1, m.property.1⟩) :=
  Implementation.allFirst scalar scalar (by decide) (by decide)
private def corrInput := core.scalarAll.prod core.messageAll (by decide)
private def corrScalar : Implementation .unit corrInput core.scalarAll Prod.fst :=
  Implementation.first (by decide) core.scalarAll core.messageAll (by decide) (by decide)
private def corrMessage : Implementation .unit corrInput core.scalarAll (fun value => ⟨value.2.val.2, value.2.property.2⟩) :=
  (Implementation.second (by decide) core.scalarAll core.messageAll (by decide) (by decide)).then
    (Implementation.allSecond scalar scalar (by decide) (by decide))
private def corrArgs : Implementation .unit corrInput (core.scalarAll.prod core.scalarAll (by decide))
    (fun value => (value.1, ⟨value.2.val.2, value.2.property.2⟩)) :=
  corrScalar.pair' (a := 2) (b := 2) corrMessage (by decide) (Implementation.first_buffers _ _ _ _ _)
    (Implementation.then_buffers _ _ (Implementation.second_buffers _ _ _ _ _) (Implementation.allSecond_buffers _ _ _ _)) (by decide) (by decide)
/-- Scheme₁'s correction `k · m`. -/
private def corr₁ : Implementation .unit corrInput core.scalarAll (fun value => word (BinOp.mul.eval value.1.val value.2.val.2)) :=
  corrArgs.then mulAll
/-- Scheme₂'s correction `k`. -/
private def corr₂ : Implementation .unit corrInput core.scalarAll Prod.fst := corrScalar

private def fmaInput := core.scalarAll.prod (core.pointAll.prod core.pointAll (by decide)) (by decide)
private def fmaScalar : Implementation .unit fmaInput core.scalarAll Prod.fst :=
  Implementation.first (by decide) core.scalarAll (core.pointAll.prod core.pointAll (by decide)) (by decide) (by decide)
private def fmaPoints : Implementation .unit fmaInput (core.pointAll.prod core.pointAll (by decide)) Prod.snd :=
  Implementation.second (by decide) core.scalarAll (core.pointAll.prod core.pointAll (by decide)) (by decide) (by decide)
private def fmaHash : Implementation .unit fmaInput core.pointAll (fun value => value.2.1) :=
  fmaPoints.then (Implementation.first (by decide) core.pointAll core.pointAll (by decide) (by decide))
private def fmaSignature : Implementation .unit fmaInput core.pointAll (fun value => value.2.2) :=
  fmaPoints.then (Implementation.second (by decide) core.pointAll core.pointAll (by decide) (by decide))
private def fmaScaled : Implementation .unit fmaInput core.pointAll (fun value => word (BinOp.mul.eval value.1.val value.2.1.val)) :=
  (fmaScalar.pair' (a := 2) (b := 2) fmaHash (by decide) (Implementation.first_buffers _ _ _ _ _)
    (Implementation.then_buffers _ _ (Implementation.second_buffers _ _ _ _ _) (Implementation.first_buffers _ _ _ _ _)) (by decide) (by decide)).then mulAll
private theorem fmaScaled_buffers : fmaScaled.program.code.memBound ≤ 3 :=
  Implementation.then_buffers _ _ (Implementation.pair'_buffers _ _ _ _ _ _ _) mulAllNames.buffers
/-- `σ + c · h`. -/
private def fma : Implementation .unit fmaInput core.pointAll
    (fun value => word (BinOp.add.eval value.2.2.val (BinOp.mul.eval value.1.val value.2.1.val))) :=
  (fmaSignature.pair' (a := 2) (b := 3) fmaScaled (by decide)
    (Implementation.then_buffers _ _ (Implementation.second_buffers _ _ _ _ _) (Implementation.second_buffers _ _ _ _ _)) fmaScaled_buffers
    (by decide) (by decide)).then addAll

private theorem hashOf_bound : hashOf.BoundedBy 100 100 :=
  (Implementation.allFirst_boundedBy _ _ _ _).mono (by decide) (by decide)
private theorem corr₁_bound : corr₁.BoundedBy 1000 3000 := by
  refine ((Implementation.pair'_boundedBy' _ _ _ _ _ _ _ (Implementation.first_boundedBy' _ _ (le_refl _))
    ((Implementation.second_boundedBy' _ _ (le_refl _)).then (Implementation.allSecond_boundedBy' _ _ (le_refl _)))
    (le_refl _) (le_refl _) (le_refl _)).then mulAllBound).mono ?_ ?_ <;> decide
private theorem corr₂_bound : corr₂.BoundedBy 1000 3000 := (Implementation.first_boundedBy' _ _ (le_refl _)).mono (by decide) (by decide)
private theorem fma_bound : fma.BoundedBy 1000 3000 := by
  refine ((Implementation.pair'_boundedBy' _ _ _ _ _ _ _
    ((Implementation.second_boundedBy' _ _ (le_refl _)).then (Implementation.second_boundedBy' _ _ (le_refl _)))
    ((Implementation.pair'_boundedBy' _ _ _ _ _ _ _ (Implementation.first_boundedBy' _ _ (le_refl _))
      ((Implementation.second_boundedBy' _ _ (le_refl _)).then (Implementation.first_boundedBy' _ _ (le_refl _)))
      (le_refl _) (le_refl _) (le_refl _)).then mulAllBound)
    (le_refl _) (le_refl _) (le_refl _)).then addAllBound).mono ?_ ?_ <;> decide

private def routines₁ : SyncWrap.Routines core where
  hashOfFn := fun m => ⟨m.val.1, m.property.1⟩
  hashOf := hashOf
  corrFn := fun value => word (BinOp.mul.eval value.1.val value.2.val.2)
  corr := corr₁
  fmaFn := fun value => word (BinOp.add.eval value.2.2.val (BinOp.mul.eval value.1.val value.2.1.val))
  fma := fma
  slots := 4
  reserve := by decide
  hashOfBuffers := (Implementation.allFirst_buffers _ _ _ _).trans (by decide)
  corrBuffers := (Implementation.then_buffers _ _ (Implementation.pair'_buffers _ _ _ _ _ _ _) mulAllNames.buffers).trans (by decide)
  fmaBuffers := (Implementation.then_buffers _ _ (Implementation.pair'_buffers _ _ _ _ _ _ _) addAllNames.buffers).trans (by decide)
  time := 1000
  words := 3000
  hashOfBound := hashOf_bound.mono (by decide) (by decide)
  corrBound := corr₁_bound
  fmaBound := fma_bound
  hashOfNames := Implementation.allFirst_names _ _ _ _ _
  corrNames := Implementation.then_names _ _
    (Implementation.pair'_names _ _ _ _ _ _ _ (Implementation.first_names _ _ _ _ _)
      (Implementation.then_names _ _ (Implementation.second_names _ _ _ _ _) (Implementation.allSecond_names _ _ _ _ _)))
    (mulAllNames.mono (by decide)).accounted
  fmaNames := Implementation.then_names _ _
    (Implementation.pair'_names _ _ _ _ _ _ _
      (Implementation.then_names _ _ (Implementation.second_names _ _ _ _ _) (Implementation.second_names _ _ _ _ _))
      (Implementation.then_names _ _
        (Implementation.pair'_names _ _ _ _ _ _ _ (Implementation.first_names _ _ _ _ _)
          (Implementation.then_names _ _ (Implementation.second_names _ _ _ _ _) (Implementation.first_names _ _ _ _ _)))
        (mulAllNames.mono (by decide)).accounted))
    (addAllNames.mono (by decide)).accounted

/-! ## The finish routines: `k · m*`, negation, multiplication -/

private def finInput := core.scalar.prod core.message (core.fits2 (core.le3 core.scalarAll_le) (core.le3 core.messageAll_le))
private def finFirst : Implementation .unit finInput core.scalar Prod.fst :=
  Implementation.first (by decide) core.scalar core.message (by decide) (core.fits2 (core.le3 core.scalarAll_le) (core.le3 core.messageAll_le))
private def finMessage : Implementation .unit finInput core.scalar (fun value => value.2.2) :=
  (Implementation.second (by decide) core.scalar core.message (by decide) (core.fits2 (core.le3 core.scalarAll_le) (core.le3 core.messageAll_le))).then
    (Implementation.second (by decide) scalar scalar (by decide) (by decide))
private def finArgs : Implementation .unit finInput (core.scalar.prod core.scalar (by decide)) (fun value => (value.1, value.2.2)) :=
  finFirst.pair' (a := 2) (b := 2) finMessage (by decide) (Implementation.first_buffers _ _ _ _ _)
    (Implementation.then_buffers _ _ (Implementation.second_buffers _ _ _ _ _) (Implementation.second_buffers _ _ _ _ _)) (by decide) (by decide)
/-- Scheme₁'s final scalar `k · m*`. -/
private def fin₁ : Implementation .unit finInput core.scalar (fun value => BinOp.mul.eval value.1 value.2.2) := finArgs.then mul'
private def zeroScalar : Implementation .unit core.scalar core.scalar (fun _ => 0) :=
  Implementation.constant core.scalar core.scalar ⟨0, trivial⟩ (by decide)
private def negArgs : Implementation .unit core.scalar (core.scalar.prod core.scalar (by decide)) (fun value => (0, value)) :=
  zeroScalar.pair' (a := 2) (b := 0) (Implementation.identity core.scalar (by decide)) (by decide)
    (Implementation.constant_buffers _ _ _ _) (Implementation.identity_buffers _) (by decide) (by decide)
private def neg : Implementation .unit core.scalar core.scalar (fun value => BinOp.sub.eval 0 value) := negArgs.then sub'

private theorem finFirst_bound : finFirst.BoundedBy 8 40 := Implementation.first_boundedBy' _ _ (le_refl _)
private theorem finMessage_bound : finMessage.BoundedBy 24 107 :=
  (Implementation.second_boundedBy' _ _ (le_refl _)).then (Implementation.second_boundedBy' _ _ (le_refl _))
private theorem finArgs_bound : finArgs.BoundedBy 300 1200 :=
  (Implementation.pair'_boundedBy' _ _ _ _ _ _ _ finFirst_bound finMessage_bound (le_refl _) (le_refl _) (le_refl _)).mono (by decide) (by decide)
private theorem fin₁_bound : fin₁.BoundedBy 1000 3000 := (finArgs_bound.then mul'Bound).mono (by decide) (by decide)
private theorem zeroScalar_bound : zeroScalar.BoundedBy 8 40 := Implementation.constant_bounded' _ _ (le_refl _)
private theorem negArgs_bound : negArgs.BoundedBy 300 1200 :=
  (Implementation.pair'_boundedBy' _ _ _ _ _ _ _ zeroScalar_bound (Implementation.identity_boundedBy _ _) (le_refl _) (le_refl _) (le_refl _)).mono
    (by decide) (by decide)
private theorem neg_bound : neg.BoundedBy 1000 3000 := (negArgs_bound.then sub'Bound).mono (by decide) (by decide)

private def finish₁ : SyncWrap.Wrapper.FinishRoutines core where
  finFn := fun value => BinOp.mul.eval value.1 value.2.2
  fin := fin₁
  negFn := fun value => BinOp.sub.eval 0 value
  neg := neg
  mulFn := fun value => BinOp.mul.eval value.1 value.2
  mul := mul'
  slots := 4
  reserve := by decide
  finBuffers := (Implementation.then_buffers _ _ (Implementation.pair'_buffers _ _ _ _ _ _ _) mul'Names.buffers).trans (by decide)
  negBuffers := (Implementation.then_buffers _ _ (Implementation.pair'_buffers _ _ _ _ _ _ _) sub'Names.buffers).trans (by decide)
  mulBuffers := mul'Names.buffers.trans (by decide)
  time := 1000
  words := 3000
  finBound := fin₁_bound
  negBound := neg_bound
  mulBound := mul'Bound.mono (by decide) (by decide)
  finNames := Implementation.then_names _ _
    (Implementation.pair'_names _ _ _ _ _ _ _ (Implementation.first_names _ _ _ _ _)
      (Implementation.then_names _ _ (Implementation.second_names _ _ _ _ _) (Implementation.second_names _ _ _ _ _)))
    (mul'Names.mono (by decide)).accounted
  negNames := Implementation.then_names _ _
    (Implementation.pair'_names _ _ _ _ _ _ _ (Implementation.constant_names _ _ _ _ _) (Implementation.identity_names _ _))
    (sub'Names.mono (by decide)).accounted
  mulNames := (mul'Names.mono (by decide)).accounted

/-! ## A trivial inner caller: one signing query, then the forgery it started with -/

private abbrev Forgery := scheme.goodBounds.extraction.forgery.Value
private def forgery (target : Key × Word 64) (beta : Word 64) (gamma xi : List (Word 64))
    (gammaFits : gamma.length ≤ 6) (xiFits : xi.length ≤ 6) : Forgery :=
  ⟨(target, beta, gamma, xi), ⟨trivial, trivial⟩, trivial, ⟨gammaFits, fun _ _ => trivial⟩, xiFits, fun _ _ => trivial⟩
private def signRequest : core.inner.good.Request := .inr (.inr ⟨(7, 3), trivial, trivial⟩)
private def head : core.inner.good.forgery.Value ⊕ (core.inner.good.Request × Forgery) :=
  .inr (signRequest, forgery (7, 3) 11 [5] [2] (by decide) (by decide))
private def innerAdvance (value : Forgery × core.inner.good.Reply) : core.inner.good.forgery.Value ⊕ (core.inner.good.Request × Forgery) :=
  .inl value.1
private def innerContinuation : Realizer .unit (CallerStep.resume core.inner.good.control) (CallerStep.next core.inner.good.control) innerAdvance :=
  (firstRealizer .unit (by decide) core.inner.state
    (WeightedCallerPackets.reply core.inner.good.service core.inner.randomBound core.inner.randomFits) (by decide) (by decide)).then
    (inlRealizer .unit (by decide) core.inner.good.forgery.representation (CallerStep.pending core.inner.good.control) (by decide) (by decide))
private def continuationRaw : Stmt 64 := selectSlice 0 17 ;; Assembly.code (Construction.taggedOperands 0 17 4)
private theorem continuation_code : innerContinuation.code = continuationRaw := rfl
private theorem continuation_words : descriptionWords innerContinuation.code ≤ 3000 := by
  have raw := Assembly.code_descriptionWords_le (Construction.taggedOperands (w := 64) 0 17 4)
  change descriptionWords (Assembly.code (Construction.taggedOperands (w := 64) 0 17 4)) ≤ 26 * 22 + 14 at raw
  rw [continuation_code, continuationRaw, descriptionWords_seq, selectSlice_descriptionWords]
  omega
private theorem continuation_names : NamesAccounted innerContinuation.code 4 := by
  have raw := Assembly.code_names (Construction.taggedOperands (w := 64) 0 17 4) 1 (Construction.prefix_sources 0 17 4)
  rw [continuation_code]
  exact (selectSlice_names 0 17 4).seq (show NamesBound _ 4 from ⟨raw.1.trans (by decide), raw.2.trans (by decide)⟩).accounted
private theorem continuation_buffers : innerContinuation.code.memBound ≤ 3004 := by
  have names := continuation_names.buffers
  have words := continuation_words
  omega
private def innerInitial := Implementation.constant core.inner.key (Layout.all (CallerStep.next core.inner.good.control)) ⟨head, trivial⟩ (by decide)
private theorem initial_buffers : innerInitial.program.code.memBound ≤ 2 :=
  Implementation.constant_buffers core.inner.key (Layout.all (CallerStep.next core.inner.good.control)) ⟨head, trivial⟩ (by decide)
private def innerCaller : SharedCaller core.inner where
  advance := innerAdvance
  continuation := innerContinuation
  localNameFits := by
    change max 2 innerContinuation.code.memBound < 2 ^ 64
    have := continuation_buffers
    omega
  initial := fun _ => head
  initialCode := innerInitial.program.viewOutput (CallerStep.next core.inner.good.control) (fun _ => head) (fun _ => rfl)
  initialNameFits := by
    change max 2 innerInitial.program.code.memBound < 2 ^ 64
    have := initial_buffers
    omega
private def innerBounds : Caller.Bounds core.inner.good core.inner.goodSetup innerCaller where
  step := ⟨1000, 3000⟩
  initial := ⟨1000, 3000⟩
  localTime _ := by change continuationRaw.staticTime .unit ≤ 1000; decide
  initialTime value := ((Implementation.constant_bounded core.inner.key (Layout.all (CallerStep.next core.inner.good.control))
    ⟨head, trivial⟩ (by decide)).time_le value).trans (by decide)
  localWords := continuation_words
  initialWords := (Implementation.constant_bounded core.inner.key (Layout.all (CallerStep.next core.inner.good.control))
    ⟨head, trivial⟩ (by decide)).code_le.trans (by decide)
  slots := 4
  localNames := continuation_names
  initialNames := Implementation.constant_names core.inner.key (Layout.all (CallerStep.next core.inner.good.control)) ⟨head, trivial⟩ (by decide) 4
private theorem callerReserve : innerCaller.continuation.code.memBound + 50 < 2 ^ 64 := by
  have := continuation_buffers
  change innerContinuation.code.memBound + 50 < 2 ^ 64
  omega
private theorem initialReserve : innerCaller.initialCode.code.memBound + 50 < 2 ^ 64 := by
  have := initial_buffers
  change innerInitial.program.code.memBound + 50 < 2 ^ 64
  omega

/-! ## The wrapper as the outer caller, with its budgets -/

private def finishImpl := wrapper.finish outLe finish₁
private theorem reserve : core.slotsAll routines₁ innerCaller innerBounds (SyncWrap.Wrapper.slotsAll finish₁) +
    3000000 * core.unitW routines₁ innerCaller innerBounds (wrapper.finishWords outLe finish₁) + 2 < 2 ^ 64 := by decide
private def outerCaller : SharedCaller wrapper.outer :=
  wrapper.toCaller routines₁ innerCaller outLe finishImpl callerReserve initialReserve innerBounds
    (wrapper.finishTime outLe finish₁) (wrapper.finishWords outLe finish₁) (SyncWrap.Wrapper.slotsAll finish₁)
    (wrapper.finish_boundedBy outLe finish₁) (wrapper.finish_names outLe finish₁) reserve
private def outerBounds : Caller.Bounds wrapper.outer.good wrapper.outer.goodSetup outerCaller :=
  wrapper.bounds routines₁ innerCaller outLe finishImpl callerReserve initialReserve innerBounds
    (wrapper.finishTime outLe finish₁) (wrapper.finishWords outLe finish₁) (SyncWrap.Wrapper.slotsAll finish₁)
    (wrapper.finish_boundedBy outLe finish₁) (wrapper.finish_names outLe finish₁) reserve


/-! ## Executing the wrapper's step and initialization code -/

private def out := wrapper.outer.good.forgery
private def advanceImpl := core.advanceImpl routines₁ innerCaller out outLe finishImpl callerReserve
private def initialImpl := core.initialImpl routines₁ innerCaller out outLe initialReserve
private abbrev Output := (core.output out outLe).Value

private def execute {A : Type} (input : Representation 64 A) (code : Stmt 64) (value : A) : Option (Output × Nat) := do
  let result ← WordIO.run .unit RandomTape.zero 10000000 (.compute code) (input.initial value) []
  let answer ← (core.output out outLe).representation.encoding.decode (result.state.bufs 0).toList
  pure (answer, result.time)

private def keyValue : core.key.Value := ⟨((3, 5), 7), ⟨⟨trivial, trivial⟩, trivial⟩⟩
private def hashReply (point : Word 64) : core.inner.good.Reply := .inr ⟨point, trivial⟩

/-- Run the wrapper from the key through one signing query of the inner caller to the finished forgery. -/
private def drive : Option (List (Output × Nat)) := do
  let first ← execute core.keyAll'.representation initialImpl.program.code ⟨keyValue, trivial⟩
  let step (previous : Output) (reply : core.inner.good.Reply) : Option (Output × Nat) :=
    match previous with
    | ⟨.inr (_, state), valid⟩ => execute core.advanceInput.representation advanceImpl.program.code ⟨(state, reply), ⟨valid.2, trivial⟩⟩
    | ⟨.inl _, _⟩ => none
  let second ← step first.1 (hashReply 13)
  let third ← step second.1 (hashReply 17)
  let fourth ← step third.1 (hashReply 19)
  pure [first, second, third, fourth]

private def period (output : Output) : Option (Word 64) :=
  match output.val with
  | .inr (.inr (.inl index), _) => some index.val
  | _ => none
private def signed (output : Output) : Option (Word 64 × Word 64) :=
  match output.val with
  | .inr (.inr (.inr message), _) => some message.val
  | _ => none
private def finished (output : Output) : Option ((Word 64 × Word 64) × (Word 64 × (List (Word 64) × List (Word 64)))) :=
  match output.val with
  | .inl forged => some forged
  | _ => none

open Lean in
run_cmd do
  match drive with
  | none => throwError "the wrapper's code did not run to completion"
  | some [first, second, third, fourth] =>
    -- The inner caller asks to sign (7, 3); the wrapper first hashes the period 7.
    unless period first.1 == some 7 do throwError "initialization did not hash the signing query's period"
    -- With the hash, the wrapper forwards the signing query.
    unless signed second.1 == some (7, 3) do throwError "the wrapper did not forward the signing query"
    -- The corrected signature returns the inner forgery; the wrapper hashes the attacked period.
    unless period third.1 == some 7 do throwError "the wrapper did not hash the attacked period"
    -- The finished forgery: the signing slot carries ξ₀ · (k · m) = 2 · 21, then −(k · m*) = −21.
    unless finished fourth.1 == some ((7, 3), (11, ([42, 18446744073709551595], [2]))) do
      throwError "the finished forgery differs from the wrapped coefficients"
    for (_, time) in [first, second, third, fourth] do
      unless time ≤ 3000000 * core.unitT routines₁ innerCaller innerBounds (wrapper.finishTime outLe finish₁) do
        throwError "a wrapper step exceeded its proved budget"
  | some _ => throwError "unexpected number of steps"

end SignaturesTest.CaliperSyncWrap
