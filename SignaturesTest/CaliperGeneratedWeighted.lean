import Proofs.Runtime.Caliper.GeneratedWeightedBounds
import Proofs.Runtime.Caliper.OOPSTermsBounds
import Proofs.Runtime.Caliper.BLSRows
import Proofs.Runtime.Caliper.GeneratedWeightedOracle
import Proofs.Runtime.Caliper.UniformSampling
import Proofs.Runtime.Caliper.UniformSamplingBounds
import Proofs.Runtime.Caliper.WeightedSignBounds
import Proofs.Runtime.Caliper.WeightedHashBounds
import Proofs.Runtime.Caliper.WeightedCapacity
import Proofs.Runtime.Caliper.WeightedOracleMemory
import Proofs.Runtime.Caliper.WeightedOracleInvariant
import Proofs.Runtime.Caliper.WeightedOracleOriginal
import Proofs.Runtime.Caliper.WeightedCallerBounds
import Proofs.Runtime.Caliper.WeightedCallerInvariant
import Proofs.Runtime.Caliper.WeightedCallerOriginal
import Proofs.Runtime.Caliper.WeightedCaller
import Proofs.Runtime.Caliper.WeightedCallerPostcondition
import Proofs.Runtime.Caliper.WeightedCallerResources
import Proofs.Runtime.Caliper.WeightedCoefficientBounds
import Proofs.Runtime.Caliper.WeightedExtractionMemory
import Proofs.Runtime.Caliper.WeightedTargetSource
import Proofs.Runtime.Caliper.WeightedTargetBounds
import Proofs.Runtime.Caliper.WeightedSignatureTailSource
import Proofs.Runtime.Caliper.WeightedSignatureTailMemory
import Proofs.Runtime.Caliper.WeightedExtractorSource
import Proofs.Runtime.Caliper.WeightedExtractorMemory
import Proofs.Runtime.Caliper.BLSExtractArithmeticNames
import Proofs.Runtime.Caliper.BLSResponseBounds
import Proofs.Runtime.Caliper.BLSResponseNames
import Mathlib.Data.BitVec
import Lean

/-! Run term generation and lazy evaluation as one actual Caliper program.
Word arithmetic exercises the implementation; no field assumption is made
about this finite fixture. Both scalar and pair caches preserve query order. -/
namespace SignaturesTest.CaliperGeneratedWeighted
open Caliper OracleComp OracleSpec Signatures.Runtime Signatures.Runtime.CaliperBackend BoundedSource

private def scalar : Layout 16 (Word 16) := Layout.all (wordRepresentation 16 (by decide))
private def oops : OOPSTerms.Layouts 16 (Word 16) (Word 16) 3 :=
  ⟨scalar, scalar, by decide, by decide, by decide⟩
private def proximity : ProximityTerms.Layouts 16 (Word 16) (Word 16) 3 :=
  ⟨scalar, scalar, by decide, by decide, by decide⟩
private abbrev Key := Fin 4 × Word 16
private def base : Bool → Type
  | false => Key
  | true => Word 16
private instance : DecidableEq (Ty.Value base (.atom false)) := inferInstanceAs (DecidableEq Key)
private instance (n : Nat) : OfNat (Ty.Value base (.atom true)) n := inferInstanceAs (OfNat (Word 16) n)
private inductive Op : Ty Bool → Ty Bool → Type
  | equal : Op (.pair (.atom false) (.atom false)) .bool
private def primitives : Primitives base Op where
  execute instruction := match instruction with
    | .equal => fun value => decide (value.1 = value.2)
  cost _ _ := 1
private def comparison : Expr Op [.atom false, .atom false] .bool :=
  .op .equal (.pair (.var .here) (.var (.there .here)))
private theorem comparison_correct (left right : Key) :
    comparison.denote primitives (left, right, ()) = decide (left = right) := rfl

private def accumulation : BLSPrivateAccumulate.Layouts 16 Key (Word 16) where
  cache := {
    key := oops.terms.key
    value := scalar
    capacityPred := 7
    wordFits := by decide
    countFits := by decide
    storageFits := by decide }
  pairStorageFits := by decide
  scalarStorageFits := by decide
  goodStorageFits := by decide
  badStorageFits := by decide

private def binary (op : BinOp) : Implementation .unit accumulation.arithmetic.pair scalar
    (fun value => op.eval value.1 value.2) where
  preserves _ _ := trivial
  program := ((WordBinary.realizer .unit op (by decide)).viewInput accumulation.arithmetic.pair.representation
    (fun value => value.val) (fun _ => rfl)).viewOutput scalar.representation
      (fun value => ⟨op.eval value.val.1 value.val.2, trivial⟩) (fun _ => rfl)
private def mul := binary .mul
private def add := binary .add
private theorem mulBound : mul.BoundedBy 6 27 := ⟨fun _ => le_rfl, by decide⟩
private theorem addBound : add.BoundedBy 6 27 := ⟨fun _ => le_rfl, by decide⟩
private theorem mulNames : NamesBound mul.program.code 3 := ⟨by decide, by decide⟩
private theorem addNames : NamesBound add.program.code 3 := ⟨by decide, by decide⟩
private def goodUpdate := BLSPrivateAccumulate.goodUpdate accumulation mul add mulNames.buffers (by decide)
private def badUpdate := BLSPrivateAccumulate.badUpdate accumulation mul add mulNames.buffers (by decide) addNames.buffers
private theorem goodBuffers : goodUpdate.program.code.memBound ≤ 4 :=
  BLSPrivateAccumulate.goodUpdate_buffers accumulation mul add mulNames.buffers (by decide) addNames.buffers
private theorem badBuffers : badUpdate.program.code.memBound ≤ 5 :=
  BLSPrivateAccumulate.badUpdate_buffers accumulation mul add mulNames.buffers (by decide) addNames.buffers
private def oopsGenerator := OOPSTerms.implementation oops trivial mul mulNames.buffers (by decide)
private def proximityGenerator := ProximityTerms.implementation proximity trivial
private theorem oopsBound : oopsGenerator.BoundedBy (OOPSTerms.timeBudget oops 6) (OOPSTerms.codeBudget oops 27) :=
  OOPSTerms.bounded oops trivial mul mulNames.buffers (by decide) mulBound
private theorem oopsNames : NamesAccounted oopsGenerator.program.code 3 :=
  OOPSTerms.names oops trivial mul mulNames.buffers (by decide) mulNames.accounted
private theorem goodBound : goodUpdate.BoundedBy
    (BLSAccumulate.goodTime accumulation.arithmetic 6 6) (BLSAccumulate.goodCode accumulation.arithmetic 27 27) :=
  BLSAccumulate.good_bounded accumulation.arithmetic mul add mulBound addBound mulNames.buffers (by decide)
private theorem goodNames : NamesAccounted goodUpdate.program.code 3 :=
  BLSAccumulate.good_names accumulation.arithmetic 3 mul add mulNames.accounted addNames.accounted mulNames.buffers (by decide)

private def sampleSpec : OracleSpec Unit := fun _ => scalar.Value
private def replyView : (Σ _ : accumulation.cache.lookup.unit.Value, scalar.Value) ≃ scalar.Value where
  toFun := Sigma.snd
  invFun value := ⟨⟨(), trivial⟩, value⟩
  left_inv value := by rcases value with ⟨⟨position, valid⟩, answer⟩; cases position; rfl
  right_inv _ := rfl
private def port : Interactive.Port 16 sampleSpec where
  Request := accumulation.cache.lookup.unit.Value
  source _ := ()
  request := accumulation.cache.lookup.unit.representation
  reply := scalar.representation.transport replyView
private def source : OracleComp sampleSpec scalar.Value := queryBind () Pure.pure
private def draw : Interactive.Code 16 := .query
private theorem drawCorrect : Interactive.Refines port .unit accumulation.cache.lookup.unit.representation
    scalar.representation (fun _ => source) draw := by
  have projected := (Interactive.Refines.query port .unit).viewOutput scalar.representation replyView (fun _ => rfl)
  convert projected using 1 <;> rfl
private theorem drawTime : Interactive.TimeBound port .unit accumulation.cache.lookup.unit.representation draw 4 :=
  Interactive.TimeBound.query
private theorem drawWords : (draw.lower port).descriptionWords ≤ 20 := by decide
private theorem drawNames : WordIO.NamesBound (draw.lower port) 3 := ⟨by decide, by decide⟩
private theorem drawFits : (draw.lower port).DescriptionFits :=
  WordIO.exchange_descriptionFits 0 1 (by decide) (by decide)
private def pairDraw := BLSPrivateAccumulate.pairSampler (base := base) (key := .atom false) (val := .atom true)
  accumulation port draw
private def pairSource := BLSPrivateAccumulate.pairSource (base := base) (key := .atom false) (val := .atom true)
  accumulation source
private theorem pairCorrect : Interactive.Refines port .unit accumulation.bad.cache.lookup.unit.representation
    accumulation.bad.cache.value.representation (fun _ => pairSource) pairDraw :=
  PairSampling.refines (hw := accumulation.cache.wordFits) (fits := accumulation.cache.pairValueFits) drawCorrect drawCorrect

private def good := GeneratedWeighted.code (base := base) (key := .atom false) (val := .atom true)
  accumulation.good oops.input 4 (by decide) (by decide) oopsGenerator port
  ⟨99, trivial⟩ primitives comparison comparison_correct goodUpdate goodBuffers (by decide) draw
private def goodProximity := GeneratedWeighted.code (base := base) (key := .atom false) (val := .atom true)
  accumulation.good proximity.input 4 (by decide) (by decide) proximityGenerator port
  ⟨99, trivial⟩ primitives comparison comparison_correct goodUpdate goodBuffers (by decide) draw
private def bad := GeneratedWeighted.code (base := base) (key := .atom false) (val := .pair (.atom true) (.atom true))
  accumulation.bad oops.input 4 (by decide) (by decide) oopsGenerator port
  ⟨(99, 98), trivial, trivial⟩ primitives comparison comparison_correct badUpdate badBuffers (by decide) pairDraw
private def goodInput := GeneratedWeighted.input (base := base) (key := .atom false) (val := .atom true) accumulation.good oops.input (by decide)
private def proximityInput := GeneratedWeighted.input (base := base) (key := .atom false) (val := .atom true) accumulation.good proximity.input (by decide)
private def badInput := GeneratedWeighted.input (base := base) (key := .atom false) (val := .pair (.atom true) (.atom true)) accumulation.bad oops.input (by decide)
private def goodState (accumulator : Word 16) (entries : List (Key × Word 16)) (bounded : entries.length ≤ 8) :
    (WeightedRows.rows accumulation.good).state.Value :=
  ⟨(accumulator, entries), trivial, bounded, fun _ _ => ⟨⟨trivial, trivial⟩, trivial⟩⟩
private def badState : (WeightedRows.rows accumulation.bad).state.Value :=
  ⟨((0, 0), []), ⟨trivial, trivial⟩, by decide, by simp⟩
private def message : oops.input.Value := ⟨(3, 42), trivial, trivial⟩
private def vector (a b c : Word 16) : proximity.input.Value :=
  ⟨((fun i => if i.val = 0 then a else if i.val = 1 then b else c), 42), (fun _ => trivial), trivial⟩
private def entries : List (Key × Word 16) :=
  [((3, 42), 11), ((2, 42), 7), ((1, 42), 5), ((0, 42), 2)]

private theorem goodCorrect : Interactive.RefinesOn
    (GeneratedWeighted.valid (base := base) (key := .atom false) (val := .atom true) accumulation.good oops.input (generate := OOPSTerms.value)) port .unit goodInput
    (WeightedRows.rows accumulation.good).state.representation
    (GeneratedWeighted.denote (base := base) (key := .atom false) (val := .atom true) accumulation.good oops.input 4 (by decide) (by decide) oopsGenerator
      ⟨99, trivial⟩ primitives comparison comparison_correct goodUpdate goodBuffers (by decide) source) good :=
  GeneratedWeighted.refines (base := base) (key := .atom false) (val := .atom true) accumulation.good oops.input 4 (by decide) (by decide) oopsGenerator port (by decide)
    ⟨99, trivial⟩ primitives comparison comparison_correct goodUpdate goodBuffers (by decide) drawCorrect
private theorem badCorrect : Interactive.RefinesOn
    (GeneratedWeighted.valid (base := base) (key := .atom false) (val := .pair (.atom true) (.atom true)) accumulation.bad oops.input (generate := OOPSTerms.value)) port .unit badInput
    (WeightedRows.rows accumulation.bad).state.representation
    (GeneratedWeighted.denote (base := base) (key := .atom false) (val := .pair (.atom true) (.atom true)) accumulation.bad oops.input 4 (by decide) (by decide) oopsGenerator
      ⟨(99, 98), trivial, trivial⟩ primitives comparison comparison_correct badUpdate badBuffers (by decide) pairSource) bad :=
  GeneratedWeighted.refines (base := base) (key := .atom false) (val := .pair (.atom true) (.atom true)) accumulation.bad oops.input 4 (by decide) (by decide) oopsGenerator port (by decide)
    ⟨(99, 98), trivial, trivial⟩ primitives comparison comparison_correct badUpdate badBuffers (by decide) pairCorrect

private def timeBudget := GeneratedWeighted.prepareTime (base := base) (key := .atom false) (val := .atom true) accumulation.good oops.input 4 (by decide) (by decide)
  (OOPSTerms.timeBudget oops 6) + RowFold.timeBudget (base := base) (key := .atom false) (val := .atom true) (WeightedRows.rows accumulation.good) 4 4
    (BLSAccumulate.goodTime accumulation.arithmetic 6 6)
private theorem goodTime : Interactive.TimeBoundOn
    (GeneratedWeighted.valid (base := base) (key := .atom false) (val := .atom true) accumulation.good oops.input (generate := OOPSTerms.value)) port .unit goodInput good timeBudget :=
  GeneratedWeighted.time_bound (base := base) (key := .atom false) (val := .atom true) accumulation.good oops.input 4 (by decide) (by decide) oopsGenerator port (by decide)
    ⟨99, trivial⟩ primitives comparison comparison_correct goodUpdate goodBuffers (by decide) drawCorrect oopsBound drawTime goodBound
private theorem goodFits : (good.lower port).DescriptionFits :=
  GeneratedWeighted.descriptionFits (base := base) (key := .atom false) (val := .atom true) accumulation.good oops.input 4 (by decide) (by decide) oopsGenerator port
    ⟨99, trivial⟩ primitives comparison comparison_correct goodUpdate goodBuffers (by decide) draw
    (by
      have bound := OOPSTerms.buffers oops trivial mul mulNames.buffers (by decide)
      change oopsGenerator.program.code.memBound ≤ 10 at bound
      change max 2 oopsGenerator.program.code.memBound < 65536
      omega) drawFits drawNames (by decide)

private def codeBudget := GeneratedWeighted.codeBudget (base := base) (key := .atom false) (val := .atom true)
  accumulation.good oops.input 4 (by decide) (by decide) (OOPSTerms.codeBudget oops 27) 20
    (BLSAccumulate.goodCode accumulation.arithmetic 27 27)
private theorem goodMemory (tape : RandomTape 16)
    (value : GeneratedWeighted.Input (base := base) (key := .atom false) (val := .atom true) accumulation.good oops.input)
    (admitted : GeneratedWeighted.valid (base := base) (key := .atom false) (val := .atom true)
      accumulation.good oops.input (generate := OOPSTerms.value) value)
    (before : State 16) (holds : goodInput.Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result 16) (reached : some finished ∈ support (good.execute port .unit tape before)) :
    finished.time ≤ timeBudget ∧
      ∃ execution : WordIO.Exec .unit tape (good.lower port) before finished.state
          finished.trace finished.time finished.net finished.peak,
        ∀ between, execution.Visits between →
          ((good.lower port).staticWords registers buffers : Int) +
            between.liveMem (max buffers (good.lower port).memBound) ≤
              5 * codeBudget + 20 + registers + 3 * buffers + before.liveMem buffers + timeBudget := by
  obtain ⟨elapsed, answer, supported, represented, execution, memory⟩ :=
    GeneratedWeighted.resources (base := base) (key := .atom false) (val := .atom true)
      accumulation.good oops.input 4 (by decide) (by decide) oopsGenerator port
      ⟨99, trivial⟩ primitives comparison comparison_correct goodUpdate goodBuffers (by decide) draw drawCorrect (by decide)
      oopsBound drawTime drawWords goodBound oopsNames drawNames goodNames
      tape value admitted before holds registers buffers initialRegisters initialBuffers finished reached
  exact ⟨elapsed, execution, fun between visited => (memory between visited).2.2.2⟩

private def termsCode := WeightedRows.code (base := base) (key := .atom false) (val := .atom true)
  accumulation.good ⟨99, trivial⟩ primitives comparison comparison_correct goodUpdate goodBuffers (by decide) 4 port draw
private def termsInput := WeightedRows.input accumulation.good 4 (by decide) (by decide)
private def entry (key : Key) (weight : Word 16) : (WeightedRows.term accumulation.good).Value :=
  ⟨(key, weight), ⟨trivial, trivial⟩, trivial⟩
private def repeated : BoundedList (WeightedRows.term accumulation.good).Value 4 :=
  ⟨[entry (2, 42) 3, entry (2, 42) 0, entry (2, 42) 4], by decide⟩
private def empty : BoundedList (WeightedRows.term accumulation.good).Value 4 := ⟨[], by decide⟩

private def execute {A B : Type} (input : Representation 16 A) (output : Representation 16 B)
    (code : Interactive.Code 16) (value : A) (replies : List (Word 16)) := do
  let initial := input.initial value
  let before := { initial with
    bufs := fun b => if b = 200 then #[77] else initial.bufs b
    caps := fun b => if b = 200 then 4 else initial.caps b
    regs := fun r => if r = 99 then 91 else initial.regs r
    tapePos := 9 }
  let result ← WordIO.run .unit RandomTape.zero 1000000 (code.lower port) before replies
  let answer ← output.encoding.decode (result.state.bufs 0).toList
  pure (answer, result.state.bufs 200, result.state.caps 200, result.state.regs 99, result.state.tapePos,
    (List.range 40).all (fun i => result.state.caps (i + 1) == 0), result.trace, result.remaining, result.time)

open Lean in
run_cmd do
  let output := (WeightedRows.rows accumulation.good).state.representation
  let wantedTrace := [WordIO.Event.invoke, .input 2, .invoke, .input 5, .invoke, .input 7, .invoke, .input 11]
  let fixtures := [
    (good, goodInput, (message, goodState 0 [] (by decide)), [2, 5, 7, 11, 88], 377, wantedTrace, [88]),
    (good, goodInput, (message, goodState 11 entries (by decide)), [88], 388, [], [88])]
  for (code, input, value, replies, expected, trace, remaining) in fixtures do
    match execute input output code value replies with
    | none => throwError "generated OOPS evaluation failed"
    | some (answer, framed, capacity, register, tape, scratch, events, rest, time) =>
      unless answer.val == (expected, entries) && framed == #[77] && capacity == 4 && register == 91 &&
          tape == 9 && scratch && events == trace && rest == remaining && time ≤ timeBudget do
        throwError "generated OOPS lost weighted sum, cache order, framing, queries or time bound"
  for (value, expected) in [(vector 3 9 27, (377 : Word 16)), (vector 0 0 0, 2)] do
    match execute proximityInput output goodProximity (value, goodState 0 [] (by decide)) [2, 5, 7, 11] with
    | none => throwError "generated Proximity evaluation failed"
    | some (answer, framed, capacity, register, tape, scratch, events, rest, _) =>
      unless answer.val == (expected, entries) && framed == #[77] && capacity == 4 && register == 91 &&
          tape == 9 && scratch && events == wantedTrace && rest.isEmpty do
        throwError "generated Proximity dropped a zero-weight query or changed the weighted fold"
  for (terms, expected, trace, remaining) in [
      (repeated,
        ((63 : Word 16), [((2, 42), (9 : Word 16))]), [WordIO.Event.invoke, .input 9], []),
      (empty, (0, []), [], [9])] do
    match execute termsInput output termsCode (terms, goodState 0 [] (by decide)) [9] with
    | none => throwError "padded weighted-list evaluation failed"
    | some (answer, _, _, _, _, scratch, events, rest, _) =>
      unless answer.val == expected && scratch && events == trace && rest == remaining do
        throwError "weighted-list view changed duplicates, padding, zero weights or the empty fold"
  match execute badInput (WeightedRows.rows accumulation.bad).state.representation bad (message, badState)
      [2, 3, 5, 7, 11, 13, 17, 19, 88] with
  | none => throwError "generated pair evaluation failed"
  | some (answer, framed, capacity, register, tape, scratch, events, rest, _) =>
    unless answer.val == ((575, 654),
        [((3, 42), (17, 19)), ((2, 42), (11, 13)), ((1, 42), (5, 7)), ((0, 42), (2, 3))]) &&
        framed == #[77] && capacity == 4 && register == 91 && tape == 9 && scratch &&
        events == [.invoke, .input 2, .invoke, .input 3, .invoke, .input 5, .invoke, .input 7,
          .invoke, .input 11, .invoke, .input 13, .invoke, .input 17, .invoke, .input 19] && rest == [88] do
      throwError "pair evaluation lost independent samples, coordinate sums or retained state"
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``WeightedRows.input_bytes, ``WeightedRows.listCache, ``WeightedRows.cache_growth,
      ``GeneratedWeighted.refines, ``GeneratedWeighted.listCache, ``GeneratedWeighted.time_bound,
      ``GeneratedWeighted.cache_growth, ``GeneratedWeighted.code_bound, ``GeneratedWeighted.names,
      ``GeneratedWeighted.descriptionFits, ``GeneratedWeighted.resources, ``goodCorrect, ``badCorrect,
      ``goodTime, ``goodFits, ``goodMemory] do
    for dependency in (← collectAxioms name) do
      unless dependency ∈ allowed do throwError "unexpected axiom {dependency} in {name}"

-- Connect actual uniform-port execution to the original game key types.
private instance : SampleableType (Word 16) :=
  SampleableType.ofEquiv BitVec.equivFin.toEquiv.symm
private instance : SampleableType (Ty.Value base (.atom true)) :=
  inferInstanceAs (SampleableType (Word 16))
private instance : AddCommMonoid (Ty.Value base (.atom true)) :=
  inferInstanceAs (AddCommMonoid (Word 16))
private instance : SMul (Word 16) (Ty.Value base (.atom true)) :=
  inferInstanceAs (SMul (Word 16) (Word 16))

private def uniformPort := UniformQuery.port (w := 16) 65535 (by decide) (by decide)
private def uniformDraw := UniformSampling.code (w := 16) 65535 (by decide) (by decide) 65535
private def uniformSource : ProbComp scalar.Value :=
  (fun value => (⟨BitVec.ofFin value.val, trivial⟩ : scalar.Value)) <$>
    UniformSampling.source (w := 16) 65535 (by decide) (by decide) 65535
private theorem uniformCorrect : Interactive.Refines uniformPort .unit
    accumulation.cache.lookup.unit.representation scalar.representation (fun _ => uniformSource) uniformDraw :=
  (UniformSampling.refines (w := 16) 65535 (by decide) (by decide) 65535).viewOutput
    scalar.representation (fun value => ⟨BitVec.ofFin value.val, trivial⟩) (by
      intro value
      change [BitVec.ofFin value.val] = [BitVec.ofNat 16 value.val.val]
      congr 1
      apply BitVec.eq_of_toNat_eq
      exact (Nat.mod_eq_of_lt value.val.isLt).symm)
private theorem uniformLaw :
    Subtype.val <$> uniformSource = ($ᵗ (Ty.Value base (.atom true)) : ProbComp _) := by
  simp only [uniformSource, UniformSampling.source, Functor.map_map]
  rfl

private def uniformGood := GeneratedWeighted.code (base := base) (key := .atom false) (val := .atom true)
  accumulation.good oops.input 4 (by decide) (by decide) oopsGenerator uniformPort
  ⟨99, trivial⟩ primitives comparison comparison_correct goodUpdate goodBuffers (by decide) uniformDraw
private def uniformProximity := GeneratedWeighted.code (base := base) (key := .atom false) (val := .atom true)
  accumulation.good proximity.input 4 (by decide) (by decide) proximityGenerator uniformPort
  ⟨99, trivial⟩ primitives comparison comparison_correct goodUpdate goodBuffers (by decide) uniformDraw

private theorem oopsOracle
    (tape : RandomTape 16) (value : GeneratedWeighted.Input
      (base := base) (key := .atom false) (val := .atom true) accumulation.good oops.input)
    (admitted : GeneratedWeighted.valid (base := base) (key := .atom false) (val := .atom true)
      accumulation.good oops.input (generate := OOPSTerms.value) value)
    (before : State 16) (holds : goodInput.Holds value before) :
    (fun result => (fun answer => (answer.val.1, answer.val.2.map (Prod.map Prod.swap id))) <$>
        Interactive.observe (WeightedRows.rows accumulation.good).state.representation result) <$>
      uniformGood.execute uniformPort .unit tape before =
      some <$> ((fun result => (value.2.val.1 + result.1, result.2)) <$>
        (simulateQ (BLS.LazyAGM.Reduction.privateListOracle (M := Word 16 × Fin 4) (R := Word 16))
          (Model.LazyAGM.evalTerms (OOPS.LazyAGM.terms 3 value.1.val))).run
            (value.2.val.2.map (Prod.map Prod.swap id))) :=
  GeneratedWeighted.observe_equiv (base := base) (key := .atom false) (val := .atom true)
    accumulation.good oops.input 4 (by decide) (by decide) oopsGenerator
    ⟨99, trivial⟩ primitives comparison comparison_correct goodUpdate goodBuffers (by decide)
    (fun _ => rfl) uniformSource uniformLaw (Equiv.prodComm (Word 16) (Fin 4))
    (OOPS.LazyAGM.terms 3) (OOPSTerms.source 3)
    uniformPort uniformDraw uniformCorrect (by decide) tape value admitted before holds

private theorem proximityOracle
    (tape : RandomTape 16) (value : GeneratedWeighted.Input
      (base := base) (key := .atom false) (val := .atom true) accumulation.good proximity.input)
    (admitted : GeneratedWeighted.valid (base := base) (key := .atom false) (val := .atom true)
      accumulation.good proximity.input (generate := ProximityTerms.value) value)
    (before : State 16) (holds : proximityInput.Holds value before) :
    (fun result => (fun answer => (answer.val.1, answer.val.2.map (Prod.map Weights.decodeProximityKey id))) <$>
        Interactive.observe (WeightedRows.rows accumulation.good).state.representation result) <$>
      uniformProximity.execute uniformPort .unit tape before =
      some <$> ((fun result => (value.2.val.1 + result.1, result.2)) <$>
        (simulateQ (BLS.LazyAGM.Reduction.privateListOracle (M := Option (Fin 3) × Word 16) (R := Word 16))
          (Model.LazyAGM.evalTerms (Proximity.LazyAGM.terms value.1.val))).run
            (value.2.val.2.map (Prod.map Weights.decodeProximityKey id))) :=
  GeneratedWeighted.observe_equiv (base := base) (key := .atom false) (val := .atom true)
    accumulation.good proximity.input 4 (by decide) (by decide) proximityGenerator
    ⟨99, trivial⟩ primitives comparison comparison_correct goodUpdate goodBuffers (by decide)
    (fun _ => rfl) uniformSource uniformLaw (Weights.proximityKeyEquiv 3).symm
    Proximity.LazyAGM.terms ProximityTerms.source
    uniformPort uniformDraw uniformCorrect (by decide) tape value admitted before holds

open Lean in
run_cmd do
  -- A real uniform request writes its range before receiving the tagged reply.
  let value := (message, goodState 0 [] (by decide))
  let before := goodInput.initial value
  let replies : List (Word 16) := [65535, 2, 65535, 5, 65535, 7, 65535, 11, 88]
  match WordIO.run .unit RandomTape.zero 1000000 (uniformGood.lower uniformPort) before replies with
  | none => throwError "weighted uniform-port execution failed"
  | some result =>
    match (WeightedRows.rows accumulation.good).state.representation.encoding.decode (result.state.bufs 0).toList with
    | none => throwError "weighted uniform-port output did not decode"
    | some answer =>
      unless answer.val == (377, entries) && result.remaining == [88] &&
          result.trace == [.output 65535, .invoke, .input 65535, .input 2,
            .output 65535, .invoke, .input 65535, .input 5,
            .output 65535, .invoke, .input 65535, .input 7,
            .output 65535, .invoke, .input 65535, .input 11] do
        throwError "weighted uniform-port execution changed the range, replies, sum or final cache"
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``WeightedRows.sourceStep_evalTerms, ``WeightedRows.evalTerms_source,
      ``GeneratedWeighted.evalTerms_encoded, ``GeneratedWeighted.evalTerms_equiv,
      ``GeneratedWeighted.observe_equiv, ``oopsOracle, ``proximityOracle] do
    for dependency in (← collectAxioms name) do
      unless dependency ∈ allowed do throwError "unexpected axiom {dependency} in {name}"

private def groupLayout : BLSResponse.Layouts 16 (Word 16) (Word 16) :=
  ⟨scalar, scalar, by decide, by decide⟩
private def scale : Implementation .unit groupLayout.scaleArgs scalar (fun value => value.1 • value.2) := mul
private def signingResponse := BLSResponse.good groupLayout scale true
private theorem signingResponseBound : signingResponse.BoundedBy
    (BLSResponse.goodTime groupLayout 6) (BLSResponse.goodWords groupLayout 27) :=
  BLSResponse.good_bounded groupLayout scale mulBound true
private theorem signingResponseBuffers : signingResponse.program.code.memBound ≤ 3 :=
  BLSResponse.good_buffers groupLayout scale mulNames.buffers true
private theorem signingResponseNames : NamesAccounted signingResponse.program.code 3 :=
  BLSResponse.good_names groupLayout 3 scale mulNames.accounted true

private def signLayout {M : Type} (domain : Layout 16 M) (small : domain.representation.encoding.words ≤ 4) :
    WeightedSign.Layouts 16 Key M (Word 16) (Word 16) (Word 16 × Word 16) (Word 16) where
  evaluation := accumulation.good
  message := domain
  config := groupLayout.points
  point := scalar
  hashCapacity := 1
  signCapacityPred := 1
  hashCountFits := by decide
  signCountFits := by decide
  storageFits := by
    change 32 * (2 + domain.representation.encoding.words + 2 + 1 + 1 + 25 +
      (1 + 1 * (2 + 1)) + (1 + (1 + 1) * (domain.representation.encoding.words + 1))) < 65536
    omega
private def fullLayout := signLayout oops.input (by decide)
private def fullProximityLayout := signLayout proximity.input (by decide)
private def signingInput {M : Type} (domain : Layout 16 M) (small : domain.representation.encoding.words ≤ 4)
    (message : domain.Value) (cache : List (Key × Word 16)) (bounded : cache.length ≤ 4) :
    (signLayout domain small).input.Value :=
  ⟨(message.val, (3, 13), cache, [((0, 42), 9)], [(message.val, 10)]),
    ⟨message.property, ⟨trivial, trivial⟩,
      ⟨bounded.trans (by change 4 ≤ 8; decide), fun _ _ => ⟨⟨trivial, trivial⟩, trivial⟩⟩,
      ⟨by change 1 ≤ 1; decide, by intro entry member; simp only [List.mem_singleton] at member; subst entry; exact ⟨⟨trivial, trivial⟩, trivial⟩⟩,
      ⟨by change 1 ≤ 2; decide, by intro entry member; simp only [List.mem_singleton] at member; subst entry; exact ⟨message.property, trivial⟩⟩⟩,
    by change 1 ≤ 1; decide⟩
private def fullCode := WeightedSign.code (base := base) (key := .atom false) (val := .atom true)
  fullLayout ⟨0, trivial⟩ 4 (by decide) (by decide) oopsGenerator ⟨99, trivial⟩
  primitives comparison comparison_correct goodUpdate goodBuffers (by decide) uniformPort uniformDraw
  signingResponse signingResponseBuffers (by decide)
private def fullProximityCode := WeightedSign.code (base := base) (key := .atom false) (val := .atom true)
  fullProximityLayout ⟨0, trivial⟩ 4 (by decide) (by decide) proximityGenerator ⟨99, trivial⟩
  primitives comparison comparison_correct goodUpdate goodBuffers (by decide) uniformPort uniformDraw
  signingResponse signingResponseBuffers (by decide)
private def fullTime := WeightedSign.timeBudget (base := base) (key := .atom false) (val := .atom true)
  fullLayout 4 (by decide) (by decide) (OOPSTerms.timeBudget oops 6) 26
    (BLSAccumulate.goodTime accumulation.arithmetic 6 6) (BLSResponse.goodTime groupLayout 6)
private def fullWords := WeightedSign.codeBudget (base := base) (key := .atom false) (val := .atom true)
  fullLayout 4 (by decide) (by decide) (OOPSTerms.codeBudget oops 27) 125
    (BLSAccumulate.goodCode accumulation.arithmetic 27 27) (BLSResponse.goodWords groupLayout 27)
private theorem fullBound : Interactive.TimeBoundOn
    (WeightedSign.valid (base := base) (key := .atom false) (val := .atom true) fullLayout (generate := OOPSTerms.value))
    uniformPort .unit fullLayout.input.representation fullCode fullTime :=
  WeightedSign.time_bound (base := base) (key := .atom false) (val := .atom true)
    fullLayout ⟨0, trivial⟩ 4 (by decide) (by decide) oopsGenerator ⟨99, trivial⟩
    primitives comparison comparison_correct goodUpdate goodBuffers (by decide) uniformPort uniformDraw
    signingResponse signingResponseBuffers (by decide) uniformCorrect oopsBound
    (UniformSampling.time_bound (w := 16) 65535 (by decide) (by decide) 65535) goodBound signingResponseBound
private theorem fullFits : (fullCode.lower uniformPort).DescriptionFits :=
  WeightedSign.descriptionFits_of_components (base := base) (key := .atom false) (val := .atom true)
    fullLayout ⟨0, trivial⟩ 4 (by decide) (by decide) oopsGenerator ⟨99, trivial⟩
    primitives comparison comparison_correct goodUpdate goodBuffers (by decide) uniformPort uniformDraw
    signingResponse signingResponseBuffers (by decide)
    (OOPSTerms.buffers oops trivial mul mulNames.buffers (by decide)) (by decide)
    (UniformSampling.descriptionFits (w := 16) 65535 (by decide) (by decide) 65535)
    (UniformSampling.names (w := 16) 65535 (by decide) (by decide) 65535) (by decide)

private theorem fullOracle
    (tape : RandomTape 16) (value : fullLayout.input.Value)
    (admitted : WeightedSign.valid (base := base) (key := .atom false) (val := .atom true)
      fullLayout (generate := OOPSTerms.value) value)
    (before : State 16) (holds : fullLayout.input.representation.Holds value before) :
    (fun result => (fun answer => WeightedSign.decodeOutput Prod.swap answer.val) <$>
        Interactive.observe fullLayout.output.representation result) <$>
      fullCode.execute uniformPort .unit tape before =
      some <$> ((fun answer => (answer.1, value.val.2.1, answer.2)) <$>
        ((WeightedAGM.listOracle (OOPS.LazyAGM.terms 3)
          (fun scalar => scalar • value.val.2.1.1)
          (fun scalar => scalar • value.val.2.1.2)) (.inr value.val.1)).run
            (value.val.2.2.1.map (Prod.map Prod.swap id),
              value.val.2.2.2.1.map (Prod.map Prod.swap id), value.val.2.2.2.2)) :=
  WeightedSign.observe_equiv (base := base) (key := .atom false) (val := .atom true)
    fullLayout ⟨0, trivial⟩ 4 (by decide) (by decide) oopsGenerator ⟨99, trivial⟩
    primitives comparison comparison_correct goodUpdate goodBuffers (by decide)
    signingResponse signingResponseBuffers (by decide) (fun _ => rfl) rfl
    (Equiv.prodComm (Word 16) (Fin 4)) (OOPS.LazyAGM.terms 3) (OOPSTerms.source 3)
    uniformPort uniformDraw uniformSource uniformCorrect uniformLaw
    (fun scalar : Word 16 => scalar • value.val.2.1.1) tape value admitted before holds

private theorem fullMemory (tape : RandomTape 16) (value : fullLayout.input.Value)
    (admitted : WeightedSign.valid (base := base) (key := .atom false) (val := .atom true) fullLayout
      (generate := OOPSTerms.value) value)
    (before : State 16) (holds : fullLayout.input.representation.Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result 16) (reached : some finished ∈ support (fullCode.execute uniformPort .unit tape before)) :
    finished.time ≤ fullTime ∧
      ∃ execution : WordIO.Exec .unit tape (fullCode.lower uniformPort) before finished.state
          finished.trace finished.time finished.net finished.peak,
        ∀ between, execution.Visits between →
          ((fullCode.lower uniformPort).staticWords registers buffers : Int) +
            between.liveMem (max buffers (fullCode.lower uniformPort).memBound) ≤
              5 * fullWords + 20 + registers + 3 * buffers + before.liveMem buffers + fullTime := by
  obtain ⟨elapsed, answer, supported, represented, execution, memory⟩ :=
    WeightedSign.resources (base := base) (key := .atom false) (val := .atom true)
      fullLayout ⟨0, trivial⟩ 4 (by decide) (by decide) oopsGenerator ⟨99, trivial⟩
      primitives comparison comparison_correct goodUpdate goodBuffers (by decide) uniformPort uniformDraw
      signingResponse signingResponseBuffers (by decide) uniformCorrect oopsBound
      (UniformSampling.time_bound (w := 16) 65535 (by decide) (by decide) 65535)
      (UniformSampling.code_words (w := 16) 65535 (by decide) (by decide) 65535)
      goodBound signingResponseBound oopsNames
      (UniformSampling.names (w := 16) 65535 (by decide) (by decide) 65535) goodNames signingResponseNames
      tape value admitted before holds registers buffers initialRegisters initialBuffers finished reached
  exact ⟨elapsed, execution, memory⟩

private def badSigningResponse := BLSResponse.bad groupLayout scale add mulNames.buffers (by decide) addNames.buffers true
private theorem badSigningBuffers : badSigningResponse.program.code.memBound ≤ 5 :=
  BLSResponse.bad_buffers groupLayout scale add mulNames.buffers (by decide) addNames.buffers true
private theorem badSigningBound : badSigningResponse.BoundedBy
    (BLSResponse.badTime groupLayout true 6 6) (BLSResponse.badWords groupLayout true 27 27) :=
  BLSResponse.bad_bounded groupLayout scale add mulBound addBound mulNames.buffers (by decide) addNames.buffers true
private def fullBadLayout :
    WeightedSign.Layouts 16 Key (Word 16 × Word 16) (Word 16) (Word 16 × Word 16)
      (Word 16 × Word 16 × Word 16) (Word 16) where
  evaluation := accumulation.bad
  message := oops.input
  config := groupLayout.config
  point := scalar
  hashCapacity := 1
  signCapacityPred := 1
  hashCountFits := by decide
  signCountFits := by decide
  storageFits := by decide
private def uniformPairDraw := BLSPrivateAccumulate.pairSampler (base := base) (key := .atom false) (val := .atom true)
  accumulation uniformPort uniformDraw
private def uniformPairSource := BLSPrivateAccumulate.pairSource (base := base) (key := .atom false) (val := .atom true)
  accumulation uniformSource
private theorem uniformPairCorrect : Interactive.Refines uniformPort .unit accumulation.bad.cache.lookup.unit.representation
    accumulation.bad.cache.value.representation (fun _ => uniformPairSource) uniformPairDraw :=
  PairSampling.refines (hw := accumulation.cache.wordFits) (fits := accumulation.cache.pairValueFits) uniformCorrect uniformCorrect
private def fullBadInput : fullBadLayout.input.Value :=
  ⟨(message.val, (5, 3, 13), [], [((0, 42), 9)], [(message.val, 10)]),
    ⟨message.property, ⟨trivial, trivial, trivial⟩,
      ⟨by decide, by simp⟩,
      ⟨by decide, by intro entry member; simp only [List.mem_singleton] at member; subst entry; exact ⟨⟨trivial, trivial⟩, trivial⟩⟩,
      ⟨by decide, by intro entry member; simp only [List.mem_singleton] at member; subst entry; exact ⟨message.property, trivial⟩⟩⟩,
    by decide⟩
private def fullBadCode := WeightedSign.code (base := base) (key := .atom false) (val := .pair (.atom true) (.atom true))
  fullBadLayout ⟨(0, 0), trivial, trivial⟩ 4 (by decide) (by decide) oopsGenerator ⟨(99, 98), trivial, trivial⟩
  primitives comparison comparison_correct badUpdate badBuffers (by decide) uniformPort uniformPairDraw
  badSigningResponse badSigningBuffers (by decide)
private def fullBadTime := WeightedSign.timeBudget (base := base) (key := .atom false) (val := .pair (.atom true) (.atom true))
  fullBadLayout 4 (by decide) (by decide) (OOPSTerms.timeBudget oops 6) (PairSampling.timeBudget scalar scalar 26 26)
    (BLSAccumulate.badTime accumulation.arithmetic 6 6) (BLSResponse.badTime groupLayout true 6 6)
private theorem fullBadBound : Interactive.TimeBoundOn
    (WeightedSign.valid (base := base) (key := .atom false) (val := .pair (.atom true) (.atom true))
      fullBadLayout (generate := OOPSTerms.value))
    uniformPort .unit fullBadLayout.input.representation fullBadCode fullBadTime :=
  WeightedSign.time_bound (base := base) (key := .atom false) (val := .pair (.atom true) (.atom true))
    fullBadLayout ⟨(0, 0), trivial, trivial⟩ 4 (by decide) (by decide) oopsGenerator ⟨(99, 98), trivial, trivial⟩
    primitives comparison comparison_correct badUpdate badBuffers (by decide) uniformPort uniformPairDraw
    badSigningResponse badSigningBuffers (by decide) uniformPairCorrect oopsBound
    (PairSampling.time_bound uniformCorrect uniformCorrect
      (UniformSampling.time_bound (w := 16) 65535 (by decide) (by decide) 65535)
      (UniformSampling.time_bound (w := 16) 65535 (by decide) (by decide) 65535))
    (BLSAccumulate.bad_bounded accumulation.arithmetic mul add mulBound addBound mulNames.buffers (by decide) addNames.buffers)
    badSigningBound

private def executeUniform {A B : Type} (input : Representation 16 A) (output : Layout 16 B)
    (code : Interactive.Code 16) (value : A) (replies : List (Word 16)) := do
  let initial := input.initial value
  let before := { initial with
    bufs := fun buffer => if buffer = 200 then #[77] else initial.bufs buffer
    caps := fun buffer => if buffer = 200 then 4 else initial.caps buffer
    regs := fun register => if register = 99 then 91 else initial.regs register
    tapePos := 9 }
  let result ← WordIO.run .unit RandomTape.zero 1000000 (code.lower uniformPort) before replies
  let answer ← output.representation.encoding.decode (result.state.bufs 0).toList
  pure (answer.val, result.state.bufs 200, result.state.caps 200, result.state.regs 99, result.state.tapePos,
    (List.range 40).all (fun i => result.state.caps (i + 1) == 0), result.trace, result.remaining, result.time)

private def executeSigning {M : Type} {R C : Type} (layout : WeightedSign.Layouts 16 Key M (Word 16) R C (Word 16))
    (code : Interactive.Code 16) (value : layout.input.Value) (replies : List (Word 16)) :=
  executeUniform layout.input.representation layout.output code value replies

open Lean in
run_cmd do
  let fresh : List (Word 16) := [65535, 2, 65535, 5, 65535, 7, 65535, 11, 88]
  let trace := [WordIO.Event.output 65535, .invoke, .input 65535, .input 2,
    .output 65535, .invoke, .input 65535, .input 5, .output 65535, .invoke, .input 65535, .input 7,
    .output 65535, .invoke, .input 65535, .input 11]
  let caches : List {cache : List (Key × Word 16) // cache.length ≤ 4} :=
    [⟨[], by decide⟩, ⟨entries, by decide⟩]
  for cache in caches do
    let replies := if cache.val.isEmpty then fresh else [88]
    let expectedTrace := if cache.val.isEmpty then trace else []
    let value := signingInput oops.input (by decide) message cache.val cache.property
    match executeSigning fullLayout fullCode value replies with
    | none => throwError "complete weighted signing failed"
    | some (answer, framed, capacity, register, tape, scratch, events, remaining, elapsed) =>
      unless answer == (4901, (3, 13), entries, [((0, 42), 9)], [(message.val, 4901), (message.val, 10)]) &&
          framed == #[77] && capacity == 4 && register == 91 && tape == 9 && scratch &&
          events == expectedTrace && remaining == [88] && elapsed ≤ fullTime do
        throwError "signing lost response, configuration, cache, delivered logs, framing, or resource bound"
  let vectorMessage := vector 3 9 27
  let value := signingInput proximity.input (by decide) vectorMessage [] (by decide)
  match executeSigning fullProximityLayout fullProximityCode value fresh with
  | none => throwError "complete Proximity signing failed"
  | some (answer, framed, capacity, register, tape, scratch, events, remaining, _) =>
    let signatures := answer.2.2.2.2.map (fun entry => (List.ofFn entry.1.1, entry.1.2, entry.2))
    unless answer.1 == 4901 && answer.2.1 == (3, 13) && answer.2.2.1 == entries &&
        answer.2.2.2.1 == [((0, 42), 9)] && signatures == [([3, 9, 27], 42, 4901), ([3, 9, 27], 42, 10)] &&
        framed == #[77] && capacity == 4 && register == 91 && tape == 9 && scratch &&
        events == trace && remaining == [88] do
      throwError "Proximity signing changed its vector message, weighted response, log or cache"
  let pairSamples : List (Word 16) := [2, 3, 5, 7, 11, 13, 17, 19]
  let pairReplies := pairSamples.flatMap (fun value => [65535, value]) ++ [88]
  let pairTrace := pairSamples.flatMap (fun value =>
    [WordIO.Event.output 65535, .invoke, .input 65535, .input value])
  match executeSigning fullBadLayout fullBadCode fullBadInput pairReplies with
  | none => throwError "complete pair signing failed"
  | some (answer, framed, capacity, register, tape, scratch, events, remaining, elapsed) =>
    unless answer == (47185, (5, 3, 13),
        [((3, 42), (17, 19)), ((2, 42), (11, 13)), ((1, 42), (5, 7)), ((0, 42), (2, 3))],
        [((0, 42), 9)], [(message.val, 47185), (message.val, 10)]) &&
        framed == #[77] && capacity == 4 && register == 91 && tape == 9 && scratch &&
        events == pairTrace && remaining == [88] && elapsed ≤ fullBadTime do
      throwError "pair signing changed samples, coordinate sums, delivered response, framing or time bound"
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``ByteRoute.realizer, ``ByteRoute.time, ``ByteRoute.codeWords, ``GeneratedWeighted.savedNameFits,
      ``WeightedSign.refines, ``WeightedSign.denote_source, ``WeightedSign.observe,
      ``WeightedSign.denote_equiv, ``WeightedSign.observe_equiv, ``fullOracle,
      ``WeightedSign.time_bound, ``WeightedSign.code_bound, ``WeightedSign.resources,
      ``WeightedSign.descriptionFits_of_components, ``fullBound, ``fullFits, ``fullMemory, ``fullBadBound] do
    for dependency in (← collectAxioms name) do
      unless dependency ∈ allowed do throwError "unexpected axiom {dependency} in {name}"

private def fullHashLayout :
    WeightedHash.Layouts 16 Key ((Fin 3 → Word 16) × Word 16) (Word 16) (Word 16 × Word 16) (Word 16) where
  cache := accumulation.cache
  default := ⟨99, trivial⟩
  message := proximity.input
  config := groupLayout.points
  point := scalar
  hashCapacityPred := 1
  signCapacity := 1
  hashCountFits := by decide
  signCountFits := by decide
  storageFits := by decide
private def hashingResponse := BLSResponse.good groupLayout scale false
private theorem hashingBound : hashingResponse.BoundedBy
    (BLSResponse.goodTime groupLayout 6) (BLSResponse.goodWords groupLayout 27) :=
  BLSResponse.good_bounded groupLayout scale mulBound false
private theorem hashingBuffers : hashingResponse.program.code.memBound ≤ 3 :=
  BLSResponse.good_buffers groupLayout scale mulNames.buffers false
private theorem hashingNames : NamesAccounted hashingResponse.program.code 3 :=
  BLSResponse.good_names groupLayout 3 scale mulNames.accounted false
private def fullHashCode := WeightedHash.code (base := base) (key := .atom false) (val := .atom true)
  fullHashLayout primitives comparison comparison_correct uniformPort uniformDraw hashingResponse hashingBuffers (by decide)
private def fullHashTime := WeightedHash.timeBudget (base := base) (key := .atom false) (val := .atom true)
  fullHashLayout 26 (BLSResponse.goodTime groupLayout 6)
private def fullHashWords := WeightedHash.codeBudget (base := base) (key := .atom false) (val := .atom true)
  fullHashLayout 125 (BLSResponse.goodWords groupLayout 27)
private theorem fullHashBound : Interactive.TimeBound uniformPort .unit fullHashLayout.input.representation fullHashCode fullHashTime :=
  WeightedHash.time_bound (base := base) (key := .atom false) (val := .atom true)
    fullHashLayout primitives comparison comparison_correct uniformPort uniformDraw hashingResponse hashingBuffers (by decide)
    uniformCorrect (UniformSampling.time_bound (w := 16) 65535 (by decide) (by decide) 65535) hashingBound
private theorem fullHashFits : (fullHashCode.lower uniformPort).DescriptionFits :=
  WeightedHash.descriptionFits (base := base) (key := .atom false) (val := .atom true)
    fullHashLayout primitives comparison comparison_correct uniformPort uniformDraw hashingResponse hashingBuffers (by decide)
    (UniformSampling.descriptionFits (w := 16) 65535 (by decide) (by decide) 65535)
    (UniformSampling.names (w := 16) 65535 (by decide) (by decide) 65535) (by decide)
private theorem fullHashOracle (tape : RandomTape 16) (value : fullHashLayout.input.Value)
    (before : State 16) (holds : fullHashLayout.input.representation.Holds value before) :
    (fun result => (fun answer => WeightedHash.decodeOutput Weights.decodeProximityKey answer.val) <$>
        Interactive.observe fullHashLayout.output.representation result) <$>
      fullHashCode.execute uniformPort .unit tape before =
      some <$> ((fun answer => (answer.1, value.val.2.1, answer.2)) <$>
        ((WeightedAGM.listOracle Proximity.LazyAGM.terms
          (fun scalar : Word 16 => scalar • value.val.2.1.1)
          (fun scalar : Word 16 => scalar • value.val.2.1.2))
          (.inl (.inr (Weights.decodeProximityKey value.val.1)))).run
            (value.val.2.2.1.map (Prod.map Weights.decodeProximityKey id),
              value.val.2.2.2.1.map (Prod.map Weights.decodeProximityKey id), value.val.2.2.2.2)) :=
  WeightedHash.observe_equiv (base := base) (key := .atom false) (val := .atom true)
    fullHashLayout primitives comparison comparison_correct hashingResponse hashingBuffers (by decide)
    (fun scalar : Word 16 => scalar • value.val.2.1.2) (Weights.proximityKeyEquiv 3).symm Proximity.LazyAGM.terms
    uniformPort uniformDraw uniformSource uniformCorrect uniformLaw tape value before holds
private theorem fullHashMemory (tape : RandomTape 16) (value : fullHashLayout.input.Value)
    (before : State 16) (holds : fullHashLayout.input.representation.Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result 16) (reached : some finished ∈ support (fullHashCode.execute uniformPort .unit tape before)) :
    finished.time ≤ fullHashTime ∧
      ∃ execution : WordIO.Exec .unit tape (fullHashCode.lower uniformPort) before finished.state
          finished.trace finished.time finished.net finished.peak,
        ∀ between, execution.Visits between →
          ((fullHashCode.lower uniformPort).staticWords registers buffers : Int) +
            between.liveMem (max buffers (fullHashCode.lower uniformPort).memBound) ≤
              5 * fullHashWords + 20 + registers + 3 * buffers + before.liveMem buffers + fullHashTime := by
  obtain ⟨elapsed, answer, supported, represented, execution, memory⟩ :=
    WeightedHash.resources (base := base) (key := .atom false) (val := .atom true)
      fullHashLayout primitives comparison comparison_correct uniformPort uniformDraw hashingResponse hashingBuffers (by decide)
      uniformCorrect (UniformSampling.time_bound (w := 16) 65535 (by decide) (by decide) 65535)
      (UniformSampling.code_words (w := 16) 65535 (by decide) (by decide) 65535) hashingBound
      (UniformSampling.names (w := 16) 65535 (by decide) (by decide) 65535) hashingNames
      tape value before holds registers buffers initialRegisters initialBuffers finished reached
  exact ⟨elapsed, execution, memory⟩

private def fullBadHashLayout :
    WeightedHash.Layouts 16 Key (Word 16 × Word 16) (Word 16 × Word 16) (Word 16 × Word 16 × Word 16) (Word 16) where
  cache := accumulation.bad.cache
  default := ⟨(99, 98), trivial, trivial⟩
  message := oops.input
  config := groupLayout.config
  point := scalar
  hashCapacityPred := 1
  signCapacity := 1
  hashCountFits := by decide
  signCountFits := by decide
  storageFits := by decide
private def badHashResponse := BLSResponse.bad groupLayout scale add mulNames.buffers (by decide) addNames.buffers false
private theorem badHashBuffers : badHashResponse.program.code.memBound ≤ 5 :=
  BLSResponse.bad_buffers groupLayout scale add mulNames.buffers (by decide) addNames.buffers false
private def fullBadHashCode := WeightedHash.code (base := base) (key := .atom false) (val := .pair (.atom true) (.atom true))
  fullBadHashLayout primitives comparison comparison_correct uniformPort uniformPairDraw badHashResponse badHashBuffers (by decide)
private def fullBadHashTime := WeightedHash.timeBudget (base := base) (key := .atom false) (val := .pair (.atom true) (.atom true))
  fullBadHashLayout (PairSampling.timeBudget scalar scalar 26 26) (BLSResponse.badTime groupLayout false 6 6)
private theorem fullBadHashBound : Interactive.TimeBound uniformPort .unit fullBadHashLayout.input.representation fullBadHashCode fullBadHashTime :=
  WeightedHash.time_bound (base := base) (key := .atom false) (val := .pair (.atom true) (.atom true))
    fullBadHashLayout primitives comparison comparison_correct uniformPort uniformPairDraw badHashResponse badHashBuffers (by decide)
    uniformPairCorrect
    (PairSampling.time_bound uniformCorrect uniformCorrect
      (UniformSampling.time_bound (w := 16) 65535 (by decide) (by decide) 65535)
      (UniformSampling.time_bound (w := 16) 65535 (by decide) (by decide) 65535))
    (BLSResponse.bad_bounded groupLayout scale add mulBound addBound mulNames.buffers (by decide) addNames.buffers false)

private theorem hashReservation (value : fullHashLayout.input.Value) {remaining : Nat}
    (reserved : WeightedState.Reserved 8 2 1 4 (remaining + 1) value.val.2)
    (answer : fullHashLayout.output.Value)
    (reached : answer ∈ support (WeightedHash.denote (base := base) (key := .atom false) (val := .atom true)
      fullHashLayout primitives comparison comparison_correct hashingResponse uniformSource value)) :
    WeightedState.Reserved 8 2 1 4 remaining answer.val.2 :=
  (WeightedHash.growth (base := base) (key := .atom false) (val := .atom true)
    fullHashLayout primitives comparison comparison_correct hashingResponse uniformSource value answer reached).reserved_after
      reserved (by decide)

private theorem signingReservation (value : fullLayout.input.Value) {remaining : Nat}
    (reserved : WeightedState.Reserved 8 1 2 4 (remaining + 1) value.val.2)
    (answer : fullLayout.output.Value)
    (reached : answer ∈ support (WeightedSign.denote (base := base) (key := .atom false) (val := .atom true)
      fullLayout ⟨0, trivial⟩ 4 (by decide) (by decide) oopsGenerator ⟨99, trivial⟩
      primitives comparison comparison_correct goodUpdate goodBuffers (by decide) signingResponse uniformSource value)) :
    WeightedState.Reserved 8 1 2 4 remaining answer.val.2 := by
  have termBound : (OOPSTerms.value value.val.1).length ≤ 4 :=
    (oopsGenerator.preserves value.val.1 value.property.1.1).1
  have admitted : WeightedSign.valid (base := base) (key := .atom false) (val := .atom true)
      fullLayout (generate := OOPSTerms.value) value :=
    (reserved.sign_room (OOPSTerms.value value.val.1) termBound).1
  exact (WeightedSign.growth (base := base) (key := .atom false) (val := .atom true)
    fullLayout ⟨0, trivial⟩ 4 (by decide) (by decide) oopsGenerator ⟨99, trivial⟩
    primitives comparison comparison_correct goodUpdate goodBuffers (by decide) signingResponse uniformSource value admitted answer reached).reserved_after
      reserved (termBound.trans (Nat.le_max_right _ _))

private def hashRequest (key : Key) (cache : List (Key × Word 16)) (bounded : cache.length ≤ 8)
    (hashes : List (Key × Word 16)) (logBound : hashes.length ≤ 2) : fullHashLayout.plainInput.Value :=
  ⟨(key, (3, 13), cache, hashes, [((vector 3 9 27).val, 10)]),
    ⟨trivial, trivial⟩, ⟨trivial, trivial⟩,
    ⟨bounded, fun _ _ => ⟨⟨trivial, trivial⟩, trivial⟩⟩,
    ⟨logBound, fun _ _ => ⟨⟨trivial, trivial⟩, trivial⟩⟩,
    ⟨by change 1 ≤ 1; decide, by
      intro entry member
      simp only [List.mem_singleton] at member
      subst entry
      exact ⟨⟨fun _ => trivial, trivial⟩, trivial⟩⟩⟩
private def shadowed : List (Key × Word 16) :=
  entries ++ [((2, 42), 99), ((3, 42), 101), ((0, 42), 111), ((1, 42), 119)]
private def pairHashRequest : fullBadHashLayout.plainInput.Value :=
  ⟨((2, 42), (5, 3, 13), [], [((0, 42), 9)], [(message.val, 10)]),
    ⟨trivial, trivial⟩, ⟨trivial, trivial, trivial⟩, ⟨by decide, by simp⟩,
    ⟨by decide, by intro entry member; simp only [List.mem_singleton] at member; subst entry; exact ⟨⟨trivial, trivial⟩, trivial⟩⟩,
    ⟨by decide, by intro entry member; simp only [List.mem_singleton] at member; subst entry; exact ⟨message.property, trivial⟩⟩⟩

open Lean in
run_cmd do
  let caches : List {cache : List (Key × Word 16) // cache.length ≤ 8} :=
    [⟨[], by decide⟩, ⟨entries, by decide⟩, ⟨shadowed, by decide⟩]
  for cache in caches do
    let raw := hashRequest (2, 42) cache.val cache.property [((0, 42), 9)] (by decide)
    if valid : fullHashLayout.room raw.val then
      let fresh := cache.val.isEmpty
      let replies : List (Word 16) := if fresh then [65535, 7, 88] else [88]
      let wantedTrace := if fresh then [WordIO.Event.output 65535, .invoke, .input 65535, .input 7] else []
      let wantedCache := if fresh then [((2, 42), 7)] else cache.val
      match executeUniform fullHashLayout.input.representation fullHashLayout.output fullHashCode ⟨raw.val, raw.property, valid⟩ replies with
      | none => throwError "complete weighted hash failed"
      | some (answer, framed, capacity, register, tape, scratch, events, remaining, elapsed) =>
        let signatures := answer.2.2.2.2.map (fun entry => (List.ofFn entry.1.1, entry.1.2, entry.2))
        unless answer.1 == 21 && answer.2.1 == (3, 13) && answer.2.2.1 == wantedCache &&
            answer.2.2.2.1 == [((2, 42), 21), ((0, 42), 9)] && signatures == [([3, 9, 27], 42, 10)] &&
            framed == #[77] && capacity == 4 && register == 91 && tape == 9 && scratch &&
            events == wantedTrace && remaining == [88] && elapsed ≤ fullHashTime do
          throwError "hash changed source value, cache order, vector signing log, framing or resource bound"
    else throwError "hash rejected an admissible miss or full-cache hit"
  let missing := hashRequest (2, 43) shadowed (by decide) [((0, 42), 9)] (by decide)
  let fullLog := hashRequest (2, 42) entries (by decide) [((0, 42), 9), ((1, 42), 15)] (by decide)
  for invalid in [missing, fullLog] do
    if (fullHashLayout.input.representation.encoding.decode
        (fullHashLayout.plainInput.representation.encoding.encode invalid)).isSome then
      throwError "hash decoder admitted a full-cache miss or full selected log"
  let raw := pairHashRequest
  if valid : fullBadHashLayout.room raw.val then
    match executeUniform fullBadHashLayout.input.representation fullBadHashLayout.output fullBadHashCode
        ⟨raw.val, raw.property, valid⟩ [65535, 2, 65535, 3, 88] with
    | none => throwError "complete pair hash failed"
    | some (answer, framed, capacity, register, tape, scratch, events, remaining, elapsed) =>
      unless answer == (35, (5, 3, 13), [((2, 42), (2, 3))],
          [((2, 42), 35), ((0, 42), 9)], [(message.val, 10)]) &&
          framed == #[77] && capacity == 4 && register == 91 && tape == 9 && scratch &&
          events == [.output 65535, .invoke, .input 65535, .input 2, .output 65535, .invoke, .input 65535, .input 3] &&
          remaining == [88] && elapsed ≤ fullBadHashTime do
        throwError "pair hash changed independent samples, response, logs, framing or time bound"
  else throwError "pair hash rejected a represented request"
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``WeightedHash.refines, ``WeightedHash.denote_source, ``WeightedHash.observe,
      ``WeightedHash.denote_equiv, ``WeightedHash.observe_equiv, ``WeightedHash.time_bound,
      ``WeightedHash.code_bound, ``WeightedHash.descriptionFits, ``WeightedHash.resources,
      ``WeightedHash.growth, ``WeightedSign.growth, ``WeightedState.Change.reserved_after,
      ``WeightedState.Reserved.empty, ``WeightedState.Reserved.weaken, ``WeightedState.Reserved.hash_room,
      ``WeightedState.Reserved.sign_room, ``hashReservation, ``signingReservation,
      ``fullHashBound, ``fullHashFits, ``fullHashOracle, ``fullHashMemory, ``fullBadHashBound] do
    for dependency in (← collectAxioms name) do
      unless dependency ∈ allowed do throwError "unexpected axiom {dependency} in {name}"

private def serviceLayout : WeightedOracle.Layouts 16 Key (Word 16 × Word 16) (Word 16) (Word 16)
    (Word 16 × Word 16) (Word 16) :=
  ⟨accumulation.good, ⟨0, trivial⟩, ⟨99, trivial⟩, oops.input, groupLayout.points, scalar,
    1, 1, by decide, by decide, by decide⟩
private def serviceRespond (signing : Bool) (value : Word 16 × (Word 16 × Word 16)) : Word 16 :=
  value.1 • (if signing then value.2.2 else value.2.1)
private def serviceResponse (signing : Bool) :
    Implementation .unit serviceLayout.responseInput serviceLayout.point (serviceRespond signing) :=
  BLSResponse.good groupLayout scale signing
private theorem serviceResponseBuffers (signing : Bool) : (serviceResponse signing).program.code.memBound ≤ 3 :=
  BLSResponse.good_buffers groupLayout scale mulNames.buffers signing
private theorem serviceResponseBound (signing : Bool) : (serviceResponse signing).BoundedBy
    (BLSResponse.goodTime groupLayout 6) (BLSResponse.goodWords groupLayout 27) :=
  BLSResponse.good_bounded groupLayout scale mulBound signing
private theorem serviceResponseNames (signing : Bool) : NamesAccounted (serviceResponse signing).program.code 3 :=
  BLSResponse.good_names groupLayout 3 scale mulNames.accounted signing
private def serviceCode := WeightedOracle.code (base := base) (key := .atom false) (val := .atom true)
  serviceLayout 4 (by decide) (by decide) oopsGenerator 65535 (by decide) primitives comparison comparison_correct
  goodUpdate goodBuffers (by decide) uniformDraw serviceResponse serviceResponseBuffers (by decide)
private def serviceTime := WeightedOracle.timeBudget (base := base) (key := .atom false) (val := .atom true)
  serviceLayout 4 (by decide) (by decide) 65535 (by decide) (OOPSTerms.timeBudget oops 6) 26
    (BLSAccumulate.goodTime accumulation.arithmetic 6 6) (fun _ => BLSResponse.goodTime groupLayout 6)
private def serviceWords := WeightedOracle.codeBudget (base := base) (key := .atom false) (val := .atom true)
  serviceLayout 4 (by decide) (by decide) 65535 (by decide) (OOPSTerms.codeBudget oops 27) 125
    (BLSAccumulate.goodCode accumulation.arithmetic 27 27) (fun _ => BLSResponse.goodWords groupLayout 27)
private theorem serviceBound : Interactive.TimeBoundOn
    (WeightedOracle.valid (base := base) (key := .atom false) (val := .atom true) serviceLayout (generate := OOPSTerms.value) 65535)
    uniformPort .unit (serviceLayout.input 65535 (by decide)) serviceCode serviceTime :=
  WeightedOracle.time_bound (base := base) (key := .atom false) (val := .atom true)
    serviceLayout 4 (by decide) (by decide) oopsGenerator 65535 (by decide) primitives comparison comparison_correct
    goodUpdate goodBuffers (by decide) uniformDraw serviceResponse serviceResponseBuffers (by decide) uniformCorrect
    oopsBound (UniformSampling.time_bound (w := 16) 65535 (by decide) (by decide) 65535) goodBound serviceResponseBound
private theorem serviceFits : (serviceCode.lower uniformPort).DescriptionFits :=
  WeightedOracle.descriptionFits (base := base) (key := .atom false) (val := .atom true)
    serviceLayout 4 (by decide) (by decide) oopsGenerator 65535 (by decide) primitives comparison comparison_correct
    goodUpdate goodBuffers (by decide) uniformDraw serviceResponse serviceResponseBuffers (by decide)
    (OOPSTerms.buffers oops trivial mul mulNames.buffers (by decide)) (by decide)
    (UniformSampling.descriptionFits (w := 16) 65535 (by decide) (by decide) 65535)
    (UniformSampling.names (w := 16) 65535 (by decide) (by decide) 65535) (by decide)

private theorem serviceOracle (tape : RandomTape 16) (value : WeightedOracle.Input serviceLayout 65535)
    (admitted : WeightedOracle.valid (base := base) (key := .atom false) (val := .atom true)
      serviceLayout (generate := OOPSTerms.value) 65535 value)
    (before : State 16) (holds : (serviceLayout.input 65535 (by decide)).Holds value before) :
    (fun result => WeightedOracle.decodedIn serviceLayout 65535 Prod.swap <$>
        Interactive.observe (serviceLayout.output 65535 (by decide)) result) <$>
      serviceCode.execute uniformPort .unit tape before =
      some <$> ((fun answer => (WeightedOracle.answer (WeightedOracle.queryIn serviceLayout 65535 Prod.swap value) answer.1,
        (WeightedOracle.saved serviceLayout 65535 value).1, answer.2)) <$>
          ((WeightedAGM.listOracle (OOPS.LazyAGM.terms 3)
            (fun scalar => serviceRespond false (scalar, (WeightedOracle.saved serviceLayout 65535 value).1))
            (fun scalar => serviceRespond true (scalar, (WeightedOracle.saved serviceLayout 65535 value).1)))
            (WeightedOracle.queryIn serviceLayout 65535 Prod.swap value)).run
              (WeightedOracle.decodeStore Prod.swap (WeightedOracle.saved serviceLayout 65535 value)).2) :=
  WeightedOracle.observe_equiv (base := base) (key := .atom false) (val := .atom true)
    serviceLayout 4 (by decide) (by decide) oopsGenerator 65535 (by decide) primitives comparison comparison_correct
    goodUpdate goodBuffers (by decide) uniformDraw serviceResponse serviceResponseBuffers (by decide)
    (fun _ => rfl) rfl uniformSource uniformLaw (Equiv.prodComm (Word 16) (Fin 4)) (OOPS.LazyAGM.terms 3)
    (OOPSTerms.source 3) uniformCorrect tape value admitted before holds

private theorem serviceMemory (tape : RandomTape 16) (value : WeightedOracle.Input serviceLayout 65535)
    (admitted : WeightedOracle.valid (base := base) (key := .atom false) (val := .atom true)
      serviceLayout (generate := OOPSTerms.value) 65535 value)
    (before : State 16) (holds : (serviceLayout.input 65535 (by decide)).Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result 16) (reached : some finished ∈ support (serviceCode.execute uniformPort .unit tape before)) :
    finished.time ≤ serviceTime ∧
      ∃ execution : WordIO.Exec .unit tape (serviceCode.lower uniformPort) before finished.state
          finished.trace finished.time finished.net finished.peak,
        ∀ between, execution.Visits between →
          ((serviceCode.lower uniformPort).staticWords registers buffers : Int) +
            between.liveMem (max buffers (serviceCode.lower uniformPort).memBound) ≤
              5 * serviceWords + 20 + registers + 3 * buffers + before.liveMem buffers + serviceTime := by
  obtain ⟨elapsed, answer, supported, represented, execution, memory⟩ :=
    WeightedOracle.resources (base := base) (key := .atom false) (val := .atom true)
      serviceLayout 4 (by decide) (by decide) oopsGenerator 65535 (by decide) primitives comparison comparison_correct
      goodUpdate goodBuffers (by decide) uniformDraw serviceResponse serviceResponseBuffers (by decide) uniformCorrect
      oopsBound (UniformSampling.time_bound (w := 16) 65535 (by decide) (by decide) 65535)
      (UniformSampling.code_words (w := 16) 65535 (by decide) (by decide) 65535) goodBound serviceResponseBound
      oopsNames (UniformSampling.names (w := 16) 65535 (by decide) (by decide) 65535) goodNames serviceResponseNames
      tape value admitted before holds registers buffers initialRegisters initialBuffers finished reached
  exact ⟨elapsed, execution, memory⟩

private theorem serviceReady (value : WeightedOracle.Input serviceLayout 65535) {remaining : Nat}
    (reserved : WeightedOracle.Reserved serviceLayout 4 (remaining + 1) (WeightedOracle.saved serviceLayout 65535 value)) :
    WeightedOracle.valid (base := base) (key := .atom false) (val := .atom true)
      serviceLayout (generate := OOPSTerms.value) 65535 value :=
  WeightedOracle.valid_of_reserved (base := base) (key := .atom false) (val := .atom true)
    serviceLayout 4 (by decide) (by decide) oopsGenerator 65535 value reserved
private theorem serviceReservation (value : WeightedOracle.Input serviceLayout 65535) {remaining : Nat}
    (reserved : WeightedOracle.Reserved serviceLayout 4 (remaining + 1) (WeightedOracle.saved serviceLayout 65535 value))
    (answer : WeightedOracle.Output serviceLayout 65535)
    (reached : answer ∈ support (WeightedOracle.denote (base := base) (key := .atom false) (val := .atom true)
      serviceLayout 4 (by decide) (by decide) oopsGenerator 65535 primitives comparison comparison_correct
      goodUpdate goodBuffers (by decide) serviceResponse uniformSource value)) :
    WeightedOracle.Reserved serviceLayout 4 remaining (WeightedOracle.returned serviceLayout 65535 answer).val :=
  (WeightedOracle.step (base := base) (key := .atom false) (val := .atom true)
    serviceLayout 4 (by decide) (by decide) oopsGenerator 65535 primitives comparison comparison_correct
    goodUpdate goodBuffers (by decide) serviceResponse uniformSource value reserved answer reached).1

private def callerCode := WeightedCallerHandler.code (base := base) (key := .atom false) (val := .atom true)
  serviceLayout 4 (by decide) (by decide) oopsGenerator 65535 (by decide) primitives comparison comparison_correct
  goodUpdate goodBuffers (by decide) uniformDraw serviceResponse serviceResponseBuffers (by decide)
private def callerTime := WeightedCallerHandler.timeBudget (base := base) (key := .atom false) (val := .atom true)
  serviceLayout 4 (by decide) (by decide) 65535 (by decide) (OOPSTerms.timeBudget oops 6) 26
    (BLSAccumulate.goodTime accumulation.arithmetic 6 6) (fun _ => BLSResponse.goodTime groupLayout 6)
private def callerWords := WeightedCallerHandler.codeBudget (base := base) (key := .atom false) (val := .atom true)
  serviceLayout 4 (by decide) (by decide) 65535 (by decide) (OOPSTerms.codeBudget oops 27) 125
    (BLSAccumulate.goodCode accumulation.arithmetic 27 27) (fun _ => BLSResponse.goodWords groupLayout 27)
private theorem callerBound : Interactive.TimeBoundOn
    (WeightedCallerPackets.ready serviceLayout 65535 (OOPSTerms.value (degree := 3)))
    uniformPort .unit (WeightedCallerPackets.input serviceLayout 65535 (by decide)) callerCode callerTime :=
  WeightedCallerHandler.time_bound (base := base) (key := .atom false) (val := .atom true)
    serviceLayout 4 (by decide) (by decide) oopsGenerator 65535 (by decide) primitives comparison comparison_correct
    goodUpdate goodBuffers (by decide) uniformDraw serviceResponse serviceResponseBuffers (by decide) uniformCorrect
    oopsBound (UniformSampling.time_bound (w := 16) 65535 (by decide) (by decide) 65535) goodBound serviceResponseBound
private theorem callerFits : (callerCode.lower uniformPort).DescriptionFits :=
  WeightedCallerHandler.descriptionFits (base := base) (key := .atom false) (val := .atom true)
    serviceLayout 4 (by decide) (by decide) oopsGenerator 65535 (by decide) primitives comparison comparison_correct
    goodUpdate goodBuffers (by decide) uniformDraw serviceResponse serviceResponseBuffers (by decide)
    (OOPSTerms.buffers oops trivial mul mulNames.buffers (by decide)) (by decide)
    (UniformSampling.descriptionFits (w := 16) 65535 (by decide) (by decide) 65535)
    (UniformSampling.names (w := 16) 65535 (by decide) (by decide) 65535) (by decide)

private theorem callerMemory (tape : RandomTape 16) (value : WeightedCallerPackets.Packet serviceLayout 65535)
    (admitted : WeightedCallerPackets.ready serviceLayout 65535 (OOPSTerms.value (degree := 3)) value)
    (before : State 16) (holds : (WeightedCallerPackets.input serviceLayout 65535 (by decide)).Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result 16) (reached : some finished ∈ support (callerCode.execute uniformPort .unit tape before)) :
    finished.time ≤ callerTime ∧
      ∃ execution : WordIO.Exec .unit tape (callerCode.lower uniformPort) before finished.state
          finished.trace finished.time finished.net finished.peak,
        ∀ between, execution.Visits between →
          ((callerCode.lower uniformPort).staticWords registers buffers : Int) +
            between.liveMem (max buffers (callerCode.lower uniformPort).memBound) ≤
              5 * callerWords + 20 + registers + 3 * buffers + before.liveMem buffers + callerTime := by
  obtain ⟨elapsed, answer, supported, represented, execution, memory⟩ :=
    WeightedCallerHandler.resources (base := base) (key := .atom false) (val := .atom true)
      serviceLayout 4 (by decide) (by decide) oopsGenerator 65535 (by decide) primitives comparison comparison_correct
      goodUpdate goodBuffers (by decide) uniformDraw serviceResponse serviceResponseBuffers (by decide) uniformCorrect
      oopsBound (UniformSampling.time_bound (w := 16) 65535 (by decide) (by decide) 65535)
      (UniformSampling.code_words (w := 16) 65535 (by decide) (by decide) 65535) goodBound serviceResponseBound
      oopsNames (UniformSampling.names (w := 16) 65535 (by decide) (by decide) 65535) goodNames serviceResponseNames
      tape value admitted before holds registers buffers initialRegisters initialBuffers finished reached
  exact ⟨elapsed, execution, memory⟩

private theorem callerReady (value : WeightedCallerPackets.Packet serviceLayout 65535) {remaining : Nat}
    (reserved : WeightedOracle.Reserved serviceLayout 4 (remaining + 1) value.2.val) :
    WeightedCallerPackets.ready serviceLayout 65535 (OOPSTerms.value (degree := 3)) value :=
  WeightedCallerHandler.ready_of_reserved (base := base) (key := .atom false) (val := .atom true)
    serviceLayout 4 (by decide) (by decide) oopsGenerator 65535 value reserved
private theorem callerReservation (value : WeightedCallerPackets.Packet serviceLayout 65535) {remaining : Nat}
    (reserved : WeightedOracle.Reserved serviceLayout 4 (remaining + 1) value.2.val)
    (answer : WeightedCallerPackets.Reply serviceLayout 65535 × serviceLayout.store.Value)
    (reached : answer ∈ support (WeightedCallerHandler.denote (base := base) (key := .atom false) (val := .atom true)
      serviceLayout 4 (by decide) (by decide) oopsGenerator 65535 primitives comparison comparison_correct
      goodUpdate goodBuffers (by decide) serviceResponse uniformSource value)) :
    WeightedOracle.Reserved serviceLayout 4 remaining answer.2.val :=
  (WeightedCallerHandler.step (base := base) (key := .atom false) (val := .atom true)
    serviceLayout 4 (by decide) (by decide) oopsGenerator 65535 primitives comparison comparison_correct
    goodUpdate goodBuffers (by decide) serviceResponse uniformSource value reserved answer reached).1


private theorem callerOracle (tape : RandomTape 16) (value : WeightedCallerPackets.Packet serviceLayout 65535)
    (accepted : WeightedCallerPackets.ready serviceLayout 65535 (OOPSTerms.value (degree := 3)) value)
    (before : State 16) (holds : (WeightedCallerPackets.input serviceLayout 65535 (by decide)).Holds value before) :
    (fun result => WeightedCallerHandler.observedIn serviceLayout 65535 Prod.swap <$>
        Interactive.observe (WeightedCallerPackets.output serviceLayout 65535 (by decide)) result) <$>
      callerCode.execute uniformPort .unit tape before =
      some <$> ((fun result => (WeightedCallerHandler.answerIn serviceLayout 65535 Prod.swap value.1 result.1, result.2)) <$>
        ((WeightedCallerHandler.original (OOPS.LazyAGM.terms 3) serviceRespond)
          (WeightedCallerHandler.queryIn serviceLayout 65535 Prod.swap value.1)).run
            (WeightedOracle.decodeStore Prod.swap value.2.val)) :=
  WeightedCallerHandler.observe_equiv (base := base) (key := .atom false) (val := .atom true)
    serviceLayout 4 (by decide) (by decide) oopsGenerator 65535 (by decide) primitives comparison comparison_correct
    goodUpdate goodBuffers (by decide) uniformDraw serviceResponse serviceResponseBuffers (by decide)
    (fun _ => rfl) rfl uniformSource uniformLaw (Equiv.prodComm (Word 16) (Fin 4)) (OOPS.LazyAGM.terms 3)
    (OOPSTerms.source 3) uniformCorrect tape value accepted before holds

private def callerPacket {w : Nat} {K M F R C G : Type} [DecidableEq K]
    (layout : WeightedOracle.Layouts w K M F R C G) (randomBound : Nat) :
    WeightedOracle.Input layout randomBound → WeightedCallerPackets.Packet layout randomBound
  | .inl value => (.inl value.1, value.2)
  | .inr (.inl value) => (.inr (.inl ⟨value.val.1, value.property.1.1⟩), ⟨value.val.2, value.property.1.2⟩)
  | .inr (.inr value) => (.inr (.inr ⟨value.val.1, value.property.1.1⟩), ⟨value.val.2, value.property.1.2⟩)

private def callerDecoded {w : Nat} {K M F R C G : Type}
    (layout : WeightedOracle.Layouts w K M F R C G) (randomBound : Nat)
    (value : WeightedCallerPackets.Reply layout randomBound × layout.store.Value) :
    (Nat ⊕ G) × WeightedHash.Store K M R C G :=
  ((match value.1 with | .inl packet => .inl packet.2.val | .inr point => .inr point.val), value.2.val)

private def serviceInitial : serviceLayout.store.Value :=
  ⟨((3, 13), [], [], []), ⟨trivial, trivial⟩,
    ⟨by decide, by simp⟩, ⟨by decide, by simp⟩, ⟨by decide, by simp⟩⟩
private theorem serviceInitialRoom : WeightedOracle.Reserved serviceLayout 4 2 serviceInitial.val :=
  WeightedState.Reserved.empty (3, 13) 8 2 2 4 2 (by decide) (by decide) (by decide)
private def serviceHashInput (index : Key) (stored : serviceLayout.store.Value) :
    Option (WeightedOracle.Input serviceLayout 65535) :=
  if ready : serviceLayout.hashing.room (index, stored.val) then
    some (.inr (.inl ⟨(index, stored.val), ⟨⟨trivial, trivial⟩, stored.property⟩, ready⟩))
  else none
private def serviceSignInput (message : oops.input.Value) (stored : serviceLayout.store.Value) :
    Option (WeightedOracle.Input serviceLayout 65535) :=
  if ready : serviceLayout.signing.room (message.val, stored.val) then
    if stored.val.2.1.length + (OOPSTerms.value (degree := 3) message.val).length ≤ 8 then
      some (.inr (.inr ⟨(message.val, stored.val), ⟨message.property, stored.property⟩, ready⟩))
    else none
  else none

private def proximityService : WeightedOracle.Layouts 16 Key ((Fin 3 → Word 16) × Word 16) (Word 16) (Word 16)
    (Word 16 × Word 16) (Word 16) :=
  ⟨accumulation.good, ⟨0, trivial⟩, ⟨99, trivial⟩, proximity.input, groupLayout.points, scalar,
    1, 1, by decide, by decide, by decide⟩
private def proximityServiceCode := WeightedOracle.code (base := base) (key := .atom false) (val := .atom true)
  proximityService 4 (by decide) (by decide) proximityGenerator 65535 (by decide) primitives comparison comparison_correct
  goodUpdate goodBuffers (by decide) uniformDraw serviceResponse serviceResponseBuffers (by decide)
private def proximityCallerCode := WeightedCallerHandler.code (base := base) (key := .atom false) (val := .atom true)
  proximityService 4 (by decide) (by decide) proximityGenerator 65535 (by decide) primitives comparison comparison_correct
  goodUpdate goodBuffers (by decide) uniformDraw serviceResponse serviceResponseBuffers (by decide)
private def proximityServiceSign : proximityService.signing.input.Value :=
  ⟨((vector 3 9 27).val, (3, 13), [], [], []), ⟨⟨(fun _ => trivial), trivial⟩,
    ⟨trivial, trivial⟩, ⟨by decide, by simp⟩, ⟨by decide, by simp⟩, ⟨by decide, by simp⟩⟩, by decide⟩

private def adaptiveRequest := WeightedCallerPackets.request serviceLayout 65535 (by decide)
private def adaptiveReply := WeightedCallerPackets.reply serviceLayout 65535 (by decide)
private def adaptiveLayout := WeightedCaller.layout serviceLayout 65535 (by decide) adaptiveRequest scalar.representation (by decide)
private def adaptiveInitial (q : WeightedCallerPackets.Request serviceLayout 65535) :
    scalar.Value ⊕ (WeightedCallerPackets.Request serviceLayout 65535 × WeightedCallerPackets.Request serviceLayout 65535) := .inr (q, q)
private def adaptiveInitialCode : Realizer .unit adaptiveRequest (CallerStep.next adaptiveLayout) adaptiveInitial :=
  ((duplicateRealizer .unit (by decide) adaptiveRequest (by decide) (by decide)).then
    (inrRealizer .unit (by decide) scalar.representation (CallerStep.pending adaptiveLayout)
      (by decide) (by decide))).viewOutput (CallerStep.next adaptiveLayout) adaptiveInitial (fun _ => rfl)
private def randomIndex (value : UniformQuery.Reply 65535) : accumulation.cache.key.Value :=
  ⟨(0, BitVec.ofNat 16 value.2.val), trivial, trivial⟩
private def randomIndexCode : Realizer .unit uniformPort.reply accumulation.cache.key.representation randomIndex :=
  ByteRoute.realizer uniformPort.reply accumulation.cache.key.representation randomIndex
    [.literal [0], .slice 1 1] (by decide) (by exact ⟨by decide, trivial⟩) (by decide) (fun _ => rfl)
private def randomHashCode : Realizer .unit uniformPort.reply adaptiveRequest
    (fun value => .inr (.inl (randomIndex value))) := (randomIndexCode.then
  (inlRealizer .unit (by decide) accumulation.cache.key.representation oops.input.representation (by decide) (by decide))).then
    (inrRealizer .unit (by decide) uniformPort.request (WeightedCallerPackets.groupRequest serviceLayout) (by decide) (by decide))
private def adaptiveAdvance (value : WeightedCallerPackets.Request serviceLayout 65535 × WeightedCallerPackets.Reply serviceLayout 65535) :=
  match value.2 with
  | .inl random => adaptiveInitial (.inr (.inl (randomIndex random)))
  | .inr point => .inl point
private def adaptiveContinuation : Realizer .unit (CallerStep.resume adaptiveLayout) (CallerStep.next adaptiveLayout) adaptiveAdvance :=
  ((secondRealizer .unit (by decide) adaptiveRequest adaptiveReply (by decide) (by decide)).then
    (branchRealizer .unit (by decide) uniformPort.reply scalar.representation (CallerStep.next adaptiveLayout)
      (randomHashCode.then adaptiveInitialCode)
      (inlRealizer .unit (by decide) scalar.representation (CallerStep.pending adaptiveLayout) (by decide) (by decide))
      (by decide) (by decide))).viewOutput (CallerStep.next adaptiveLayout) adaptiveAdvance (by
        rintro ⟨pending, random | point⟩ <;> rfl)
private def adaptiveDomain (_ : Nat) (value : WeightedCallerPackets.Request serviceLayout 65535 × WeightedCallerPackets.Request serviceLayout 65535) :=
  value.1 = value.2
private theorem adaptiveValid (remaining : Nat) (q c) (_ : adaptiveDomain (remaining + 1) (q, c))
    (represented original) (_ : WeightedCallerHandler.replyMatches serviceLayout 65535 q represented original) :
    WeightedCaller.HeadValid serviceLayout 65535 adaptiveDomain remaining (adaptiveAdvance (c, represented)) := by
  cases represented with
  | inl random => rfl
  | inr point => trivial
private def adaptiveInput := adaptiveRequest.prod serviceLayout.store.representation (by decide)
private def adaptiveAdmitted (value : WeightedCallerPackets.Request serviceLayout 65535 × serviceLayout.store.Value) :=
  WeightedOracle.Reserved serviceLayout 4 2 value.2.val
private theorem adaptiveInitialValid (value) (_ : adaptiveAdmitted value) :
    WeightedCaller.HeadValid serviceLayout 65535 adaptiveDomain 2 (adaptiveInitial value.1) := rfl
private def adaptiveSource := WeightedCallerHandler.denote (base := base) (key := .atom false) (val := .atom true)
  serviceLayout 4 (by decide) (by decide) oopsGenerator 65535 primitives comparison comparison_correct
  goodUpdate goodBuffers (by decide) serviceResponse uniformSource
private def adaptive (fuel : Nat) := WeightedCaller.program (base := base) (key := .atom false) (val := .atom true)
  serviceLayout 4 (by decide) (by decide) oopsGenerator 65535 (by decide) primitives comparison comparison_correct
  goodUpdate goodBuffers (by decide) uniformDraw serviceResponse serviceResponseBuffers (by decide) adaptiveAdvance
  adaptiveRequest scalar.representation (by decide) adaptiveContinuation (by decide)
  adaptiveRequest adaptiveInitial adaptiveInitialCode (by decide) (by decide) fuel
private theorem adaptiveRefines : Interactive.RefinesOn adaptiveAdmitted uniformPort .unit adaptiveInput (CallerStep.output adaptiveLayout)
    (fun value => CallerControl.start adaptiveAdvance adaptiveSource 2 (adaptiveInitial value.1, value.2)) (adaptive 2) :=
  WeightedCaller.refines (base := base) (key := .atom false) (val := .atom true)
    serviceLayout 4 (by decide) (by decide) oopsGenerator 65535 (by decide) primitives comparison comparison_correct
    goodUpdate goodBuffers (by decide) uniformDraw serviceResponse serviceResponseBuffers (by decide)
    (fun _ => rfl) rfl uniformSource uniformLaw uniformCorrect adaptiveDomain adaptiveAdvance adaptiveValid
    adaptiveRequest scalar.representation (by decide) adaptiveContinuation (by decide)
    adaptiveRequest adaptiveInitial adaptiveInitialCode (by decide) (by decide) 2 adaptiveAdmitted adaptiveInitialValid (fun _ valid => valid)
private theorem adaptivePostcondition (fuel : Nat) (value : WeightedCallerPackets.Request serviceLayout 65535 × serviceLayout.store.Value)
    (reserved : WeightedOracle.Reserved serviceLayout 4 fuel value.2.val)
    (answer) (reached : answer ∈ support (CallerControl.start adaptiveAdvance adaptiveSource fuel (adaptiveInitial value.1, value.2))) :
    WeightedCaller.Postcondition serviceLayout 4 fuel value.2 answer.2 :=
  WeightedCaller.start_postcondition (base := base) (key := .atom false) (val := .atom true)
    serviceLayout 4 (by decide) (by decide) oopsGenerator 65535 primitives comparison comparison_correct
    goodUpdate goodBuffers (by decide) serviceResponse uniformSource adaptiveAdvance fuel (adaptiveInitial value.1, value.2) reserved answer reached

private theorem adaptiveLocalTime (value) : adaptiveContinuation.time value ≤ 1000 := by
  rcases value with ⟨pending, random | point⟩
  · change adaptiveContinuation.time (.inl ⟨0, Nat.zero_lt_succ _⟩, .inl ⟨⟨0, Nat.zero_lt_succ _⟩, ⟨0, Nat.zero_lt_succ _⟩⟩) ≤ 1000
    decide
  · change adaptiveContinuation.time (.inl ⟨0, Nat.zero_lt_succ _⟩, .inr ⟨0, trivial⟩) ≤ 1000
    decide
private theorem adaptiveInitialTime (value) : adaptiveInitialCode.time value ≤ 1000 := by
  change adaptiveInitialCode.time (.inl ⟨0, Nat.zero_lt_succ _⟩) ≤ 1000
  decide
private theorem adaptiveLocalWords : descriptionWords adaptiveContinuation.code ≤ 5000 := by decide +kernel
private theorem adaptiveInitialWords : descriptionWords adaptiveInitialCode.code ≤ 5000 := by decide +kernel
private theorem adaptiveLocalNames : NamesBound adaptiveContinuation.code 5 := ⟨by decide, by decide⟩
private theorem adaptiveInitialNames : NamesBound adaptiveInitialCode.code 5 := ⟨by decide, by decide⟩
private def adaptiveTimeBudget (fuel : Nat) := WeightedCaller.timeBudget (base := base) (key := .atom false) (val := .atom true)
  serviceLayout 4 (by decide) (by decide) 65535 (by decide) adaptiveRequest.encoding.words (CallerStep.width adaptiveLayout)
  (OOPSTerms.timeBudget oops 6) 26 (BLSAccumulate.goodTime accumulation.arithmetic 6 6)
  (fun _ => BLSResponse.goodTime groupLayout 6) 1000 1000 fuel
private def adaptiveWordsBudget (fuel : Nat) := WeightedCaller.codeBudget (base := base) (key := .atom false) (val := .atom true)
  serviceLayout 4 (by decide) (by decide) 65535 (by decide) adaptiveRequest.encoding.words (CallerStep.width adaptiveLayout)
  (OOPSTerms.codeBudget oops 27) 125 (BLSAccumulate.goodCode accumulation.arithmetic 27 27)
  (fun _ => BLSResponse.goodWords groupLayout 27) 5000 5000 fuel
private theorem adaptiveTimeBound (fuel : Nat) : Interactive.TimeBoundOn
    (fun value : WeightedCallerPackets.Request serviceLayout 65535 × serviceLayout.store.Value =>
      WeightedOracle.Reserved serviceLayout 4 fuel value.2.val)
    uniformPort .unit adaptiveInput (adaptive fuel) (adaptiveTimeBudget fuel) :=
  WeightedCaller.time (base := base) (key := .atom false) (val := .atom true)
    serviceLayout 4 (by decide) (by decide) oopsGenerator 65535 (by decide) primitives comparison comparison_correct
    goodUpdate goodBuffers (by decide) uniformDraw serviceResponse serviceResponseBuffers (by decide)
    (fun _ => rfl) rfl uniformSource uniformLaw uniformCorrect adaptiveDomain adaptiveAdvance adaptiveValid
    adaptiveRequest scalar.representation (by decide) adaptiveContinuation (by decide)
    adaptiveRequest adaptiveInitial adaptiveInitialCode (by decide) (by decide)
    oopsBound goodBound (UniformSampling.time_bound (w := 16) 65535 (by decide) (by decide) 65535)
    serviceResponseBound adaptiveLocalTime adaptiveInitialTime fuel _ (fun _ _ => rfl) (fun _ valid => valid)
private theorem adaptiveWordsBound (fuel : Nat) : ( (adaptive fuel).lower uniformPort).descriptionWords ≤ adaptiveWordsBudget fuel :=
  WeightedCaller.words (base := base) (key := .atom false) (val := .atom true)
    serviceLayout 4 (by decide) (by decide) oopsGenerator 65535 (by decide) primitives comparison comparison_correct
    goodUpdate goodBuffers (by decide) uniformDraw serviceResponse serviceResponseBuffers (by decide) adaptiveAdvance
    adaptiveRequest scalar.representation (by decide) adaptiveContinuation (by decide)
    adaptiveRequest adaptiveInitial adaptiveInitialCode (by decide) (by decide)
    oopsBound goodBound (UniformSampling.code_words (w := 16) 65535 (by decide) (by decide) 65535)
    serviceResponseBound adaptiveLocalWords adaptiveInitialWords fuel
private theorem adaptiveFits (fuel : Nat) : ((adaptive fuel).lower uniformPort).DescriptionFits :=
  WeightedCaller.descriptionFits (base := base) (key := .atom false) (val := .atom true)
    serviceLayout 4 (by decide) (by decide) oopsGenerator 65535 (by decide) primitives comparison comparison_correct
    goodUpdate goodBuffers (by decide) uniformDraw serviceResponse serviceResponseBuffers (by decide) adaptiveAdvance
    adaptiveRequest scalar.representation (by decide) adaptiveContinuation (by decide)
    adaptiveRequest adaptiveInitial adaptiveInitialCode (by decide) (by decide)
    (OOPSTerms.buffers oops trivial mul mulNames.buffers (by decide)) (by decide)
    (UniformSampling.descriptionFits (w := 16) 65535 (by decide) (by decide) 65535)
    (UniformSampling.names (w := 16) 65535 (by decide) (by decide) 65535) (by decide) (by decide +kernel) fuel
private theorem adaptiveMemory (tape : RandomTape 16) (value) (valid : adaptiveAdmitted value)
    (before : State 16) (holds : adaptiveInput.Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result 16) (reached : some finished ∈ support ((adaptive 2).execute uniformPort .unit tape before)) :
    finished.time ≤ adaptiveTimeBudget 2 ∧
      ∃ execution : WordIO.Exec .unit tape ((adaptive 2).lower uniformPort) before finished.state
          finished.trace finished.time finished.net finished.peak,
        ∀ between, execution.Visits between →
          (((adaptive 2).lower uniformPort).staticWords registers buffers : Int) +
            between.liveMem (max buffers ((adaptive 2).lower uniformPort).memBound) ≤
              5 * adaptiveWordsBudget 2 + 20 + registers + 3 * buffers + before.liveMem buffers + adaptiveTimeBudget 2 := by
  obtain ⟨elapsed, answer, supported, represented, execution, memory⟩ :=
    WeightedCaller.resources (base := base) (key := .atom false) (val := .atom true)
      serviceLayout 4 (by decide) (by decide) oopsGenerator 65535 (by decide) primitives comparison comparison_correct
      goodUpdate goodBuffers (by decide) uniformDraw serviceResponse serviceResponseBuffers (by decide)
      (fun _ => rfl) rfl uniformSource uniformLaw uniformCorrect adaptiveDomain adaptiveAdvance adaptiveValid
      adaptiveRequest scalar.representation (by decide) adaptiveContinuation (by decide)
      adaptiveRequest adaptiveInitial adaptiveInitialCode (by decide) (by decide)
      oopsBound goodBound (UniformSampling.time_bound (w := 16) 65535 (by decide) (by decide) 65535)
      (UniformSampling.code_words (w := 16) 65535 (by decide) (by decide) 65535)
      serviceResponseBound adaptiveLocalTime adaptiveInitialTime adaptiveLocalWords adaptiveInitialWords
      2 adaptiveAdmitted adaptiveInitialValid (fun _ valid => valid) (callerSlots := 5) (by decide)
      oopsNames (UniformSampling.names (w := 16) 65535 (by decide) (by decide) 65535) goodNames serviceResponseNames
      (by decide) (by decide) (by decide) (by decide) adaptiveLocalNames.accounted adaptiveInitialNames.accounted
      tape value valid before holds registers buffers initialRegisters initialBuffers finished reached
  refine ⟨elapsed, execution, ?_⟩
  intro between visited
  have bound := (memory between visited).2.2.2
  change (((adaptive 2).lower uniformPort).staticWords registers buffers : Int) +
    between.liveMem (max buffers ((adaptive 2).lower uniformPort).memBound) ≤
      adaptiveWordsBudget 2 + 4 * (5 + adaptiveWordsBudget 2) + registers + 3 * buffers +
        before.liveMem buffers + adaptiveTimeBudget 2 at bound
  omega
private theorem adaptiveExecutedPostcondition (tape : RandomTape 16) (value) (valid : adaptiveAdmitted value)
    (before : State 16) (holds : adaptiveInput.Holds value before)
    (finished : WordIO.Result 16) (reached : some finished ∈ support ((adaptive 2).execute uniformPort .unit tape before)) :
    ∃ answer, (CallerStep.output adaptiveLayout).Holds answer finished.state ∧
      WeightedCaller.Postcondition serviceLayout 4 2 value.2 answer.2 ∧
      WordIO.Exec .unit tape ((adaptive 2).lower uniformPort) before finished.state finished.trace finished.time finished.net finished.peak :=
  WeightedCaller.execution_postcondition (base := base) (key := .atom false) (val := .atom true)
    serviceLayout 4 (by decide) (by decide) oopsGenerator 65535 (by decide) primitives comparison comparison_correct
    goodUpdate goodBuffers (by decide) uniformDraw serviceResponse serviceResponseBuffers (by decide)
    (fun _ => rfl) rfl uniformSource uniformLaw uniformCorrect adaptiveDomain adaptiveAdvance adaptiveValid
    adaptiveRequest scalar.representation (by decide) adaptiveContinuation (by decide)
    adaptiveRequest adaptiveInitial adaptiveInitialCode (by decide) (by decide) 2 adaptiveAdmitted adaptiveInitialValid (fun _ valid => valid)
    tape value valid before holds finished reached

open Lean in
run_cmd do
  -- The harness chooses successive requests; each service call executes all
  -- dispatch, forwarding, cache, response and recording instructions.
  let run (value : WeightedOracle.Input serviceLayout 65535) (replies : List (Word 16))
      (wanted : (Nat ⊕ Word 16) × WeightedHash.Store Key (Word 16 × Word 16) (Word 16) (Word 16 × Word 16) (Word 16))
      (trace : List (WordIO.Event 16)) (range : Option Nat) :
      Lean.Elab.Command.CommandElabM serviceLayout.store.Value := do
    match executeUniform (serviceLayout.input 65535 (by decide)) (Layout.all (serviceLayout.output 65535 (by decide)))
        serviceCode value replies with
    | none => throwError "combined weighted service execution failed"
    | some (answer, framed, capacity, register, tape, scratch, events, remaining, elapsed) =>
      let actualRange := match answer with | .inl value => some value.1.1.val | .inr _ => none
      unless WeightedOracle.decoded serviceLayout 65535 answer == wanted && actualRange == range &&
          framed == #[77] && capacity == 4 && register == 91 && tape == 9 && scratch &&
          events == trace && remaining == [88] && elapsed ≤ serviceTime do
        throwError "combined service changed its reply, state, range, framing, trace or time bound"
      match executeUniform (WeightedCallerPackets.input serviceLayout 65535 (by decide))
          (Layout.all (WeightedCallerPackets.output serviceLayout 65535 (by decide)))
          callerCode (callerPacket serviceLayout 65535 value) replies with
      | none => throwError "caller-facing weighted handler execution failed"
      | some (reply, callerFrame, callerCapacity, callerRegister, callerTape, callerScratch, callerEvents, callerRemaining, callerElapsed) =>
        let callerRange := match reply.1 with | .inl value => some value.1.val | .inr _ => none
        unless callerDecoded serviceLayout 65535 reply == wanted && callerRange == range &&
            callerFrame == #[77] && callerCapacity == 4 && callerRegister == 91 && callerTape == 9 && callerScratch &&
            callerEvents == trace && callerRemaining == [88] && callerElapsed ≤ callerTime do
          throwError "caller packet conversion changed its reply, store, range, framing, trace or charged time"
        pure reply.2
  let stored ← run (.inl (⟨7, by decide⟩, serviceInitial)) [7, 3, 88] (.inl 3, serviceInitial.val)
    [.output 7, .invoke, .input 7, .input 3] (some 7)
  let hashed ← match serviceHashInput (2, 42) stored with
    | some value => pure value
    | none => throwError "combined hash was unexpectedly unready"
  let stored ← run hashed [65535, 7, 88] (.inr 21, (3, 13), [((2, 42), 7)], [((2, 42), 21)], [])
    [.output 65535, .invoke, .input 65535, .input 7] none
  let signed ← match serviceSignInput message stored with
    | some value => pure value
    | none => throwError "combined signing was unexpectedly unready"
  let cache : List (Key × Word 16) := [((3, 42), 11), ((1, 42), 5), ((0, 42), 2), ((2, 42), 7)]
  let stored ← run signed [65535, 2, 65535, 5, 65535, 11, 88]
    (.inr 4901, (3, 13), cache, [((2, 42), 21)], [(message.val, 4901)])
    [.output 65535, .invoke, .input 65535, .input 2, .output 65535, .invoke, .input 65535, .input 5,
      .output 65535, .invoke, .input 65535, .input 11] none
  let hashed ← match serviceHashInput (2, 42) stored with
    | some value => pure value
    | none => throwError "combined cache hit was unexpectedly unready"
  let stored ← run hashed [88] (.inr 21, (3, 13), cache, [((2, 42), 21), ((2, 42), 21)], [(message.val, 4901)]) [] none
  let signed ← match serviceSignInput message stored with
    | some value => pure value
    | none => throwError "combined cached signing was unexpectedly unready"
  let stored ← run signed [88] (.inr 4901, (3, 13), cache, [((2, 42), 21), ((2, 42), 21)],
    [(message.val, 4901), (message.val, 4901)]) [] none
  if (serviceHashInput (2, 42) stored).isSome || (serviceSignInput message stored).isSome then
    throwError "combined service admitted an exhausted selected reply log"
  let reject (value : WeightedCallerPackets.Packet serviceLayout 65535) : Lean.Elab.Command.CommandElabM Unit := do
    let bytes := (WeightedCallerPackets.input serviceLayout 65535 (by decide)).encoding.encode value
    if ((WeightedCallerHandler.admitted serviceLayout 65535 (by decide) (OOPSTerms.value (degree := 3))).encoding.decode bytes).isSome then
      throwError "caller readiness decoder admitted an exhausted selected reply log"
  reject (.inr (.inl ⟨(2, 42), trivial, trivial⟩), stored)
  reject (.inr (.inr message), stored)
  let _ ← run (.inl (⟨0, by decide⟩, stored)) [0, 0, 88] (.inl 0, stored.val)
    [.output 0, .invoke, .input 0, .input 0] (some 0)
  match executeUniform (proximityService.input 65535 (by decide)) (Layout.all (proximityService.output 65535 (by decide)))
      proximityServiceCode (.inr (.inr proximityServiceSign)) [65535, 2, 65535, 5, 65535, 7, 65535, 11, 88] with
  | none => throwError "combined Proximity service failed"
  | some (answer, framed, capacity, register, tape, scratch, events, remaining, _) =>
    match answer with
    | .inl _ => throwError "Proximity signing returned a random-reply tag"
    | .inr answer =>
      let signatures := answer.val.2.2.2.2.map (fun entry => (List.ofFn entry.1.1, entry.1.2, entry.2))
      unless answer.val.1 == 4901 && answer.val.2.1 == (3, 13) && answer.val.2.2.1 == entries &&
          answer.val.2.2.2.1.isEmpty && signatures == [([3, 9, 27], 42, 4901)] &&
          framed == #[77] && capacity == 4 && register == 91 && tape == 9 && scratch &&
          events == [.output 65535, .invoke, .input 65535, .input 2, .output 65535, .invoke, .input 65535, .input 5,
            .output 65535, .invoke, .input 65535, .input 7, .output 65535, .invoke, .input 65535, .input 11] &&
          remaining == [88] do
        throwError "combined Proximity service changed vector logs, private cache or caller state"
      match executeUniform (WeightedCallerPackets.input proximityService 65535 (by decide))
          (Layout.all (WeightedCallerPackets.output proximityService 65535 (by decide)))
          proximityCallerCode (callerPacket proximityService 65535 (.inr (.inr proximityServiceSign)))
          [65535, 2, 65535, 5, 65535, 7, 65535, 11, 88] with
      | none => throwError "caller-facing Proximity handler failed"
      | some (reply, callerFrame, callerCapacity, callerRegister, callerTape, callerScratch, callerEvents, callerRemaining, _) =>
        let signatures := reply.2.val.2.2.2.map (fun entry => (List.ofFn entry.1.1, entry.1.2, entry.2))
        unless WeightedCallerHandler.replyValue proximityService 65535 reply.1 == .inr 4901 &&
            reply.2.val.1 == (3, 13) && reply.2.val.2.1 == entries && reply.2.val.2.2.1.isEmpty &&
            signatures == [([3, 9, 27], 42, 4901)] && callerFrame == #[77] && callerCapacity == 4 &&
            callerRegister == 91 && callerTape == 9 && callerScratch && callerEvents == events &&
            callerRemaining == [88] do
          throwError "Proximity packet conversion changed vector logs, cache, trace or caller state"
  -- Here the next request is chosen by executed caller code from the reply.
  for chosen in [3, 5] do
    for fuel in [0, 1, 2] do
      let initial : WeightedCallerPackets.Request serviceLayout 65535 := .inl ⟨7, by decide⟩
      let replies : List (Word 16) := if fuel == 0 then [88] else if fuel == 1 then [7, BitVec.ofNat 16 chosen, 88]
        else [7, BitVec.ofNat 16 chosen, 65535, 7, 88]
      match executeUniform adaptiveInput (Layout.all (CallerStep.output adaptiveLayout))
          (adaptive fuel) (initial, serviceInitial) replies with
      | none => throwError "generated adaptive weighted caller failed"
      | some (answer, framed, capacity, register, tape, scratch, events, remaining, elapsed) =>
        let next : WeightedCallerPackets.Request serviceLayout 65535 :=
          if fuel == 0 then initial else .inr (.inl ⟨(0, BitVec.ofNat 16 chosen), trivial, trivial⟩)
        let correctHead := match answer.1 with
          | .inl point => fuel == 2 && point.val == 21
          | .inr pending => fuel < 2 && pending.1 == next && pending.2 == next
        let expected : WeightedHash.Store Key (Word 16 × Word 16) (Word 16) (Word 16 × Word 16) (Word 16) :=
          if fuel < 2 then serviceInitial.val else
            ((3, 13), [((0, BitVec.ofNat 16 chosen), 7)], [((0, BitVec.ofNat 16 chosen), 21)], [])
        let trace : List (WordIO.Event 16) := if fuel == 0 then [] else
          [.output 7, .invoke, .input 7, .input (BitVec.ofNat 16 chosen)] ++
            (if fuel == 1 then [] else [.output 65535, .invoke, .input 65535, .input 7])
        unless correctHead && answer.2.val == expected && framed == #[77] && capacity == 4 && register == 91 &&
            tape == 9 && scratch && events == trace && remaining == [88] && elapsed ≤ adaptiveTimeBudget fuel do
          throwError "adaptive caller lost its chosen query, cutoff, store, trace or frame"
  for fuel in [1, 2] do
    match executeUniform adaptiveInput (Layout.all (CallerStep.output adaptiveLayout))
        (adaptive fuel) (.inr (.inr message), serviceInitial) [65535, 2, 65535, 5, 65535, 7, 65535, 11, 88] with
    | none => throwError "generated weighted signing caller failed"
    | some (answer, framed, capacity, register, tape, scratch, events, remaining, elapsed) =>
      let correctHead := match answer.1 with | .inl point => point.val == 4901 | .inr _ => false
      unless correctHead && answer.2.val == ((3, 13), entries, [], [(message.val, 4901)]) &&
          framed == #[77] && capacity == 4 && register == 91 && tape == 9 && scratch && remaining == [88] && elapsed ≤ adaptiveTimeBudget fuel &&
          events == [.output 65535, .invoke, .input 65535, .input 2, .output 65535, .invoke, .input 65535, .input 5,
            .output 65535, .invoke, .input 65535, .input 7, .output 65535, .invoke, .input 65535, .input 11] do
        throwError "weighted caller changed signing or failed to return early"
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``WeightedOracle.Layouts.hashStore, ``WeightedOracle.Layouts.hashOutput,
      ``WeightedOracle.refines, ``WeightedOracle.denote_source, ``WeightedOracle.observe,
      ``WeightedOracle.denote_equiv, ``WeightedOracle.observe_equiv, ``WeightedOracle.time_bound,
      ``WeightedOracle.code_bound, ``WeightedOracle.names, ``WeightedOracle.descriptionFits,
      ``WeightedOracle.resources, ``WeightedOracle.valid_of_reserved, ``WeightedOracle.step,
      ``serviceBound, ``serviceFits, ``serviceOracle, ``serviceMemory, ``serviceReady, ``serviceReservation, ``serviceInitialRoom,
      ``WeightedCallerPackets.request_bytes, ``WeightedCallerPackets.prepare_time, ``WeightedCallerPackets.prepare_words,
      ``WeightedCallerPackets.finish_time, ``WeightedCallerPackets.finish_words, ``WeightedCallerHandler.refines,
      ``WeightedCallerHandler.denote_source, ``WeightedCallerHandler.synchronizes, ``WeightedCallerHandler.observe_equiv,
      ``WeightedCallerHandler.time_bound, ``WeightedCallerHandler.code_bound, ``WeightedCallerHandler.names,
      ``WeightedCallerHandler.descriptionFits, ``WeightedCallerHandler.resources, ``WeightedCallerHandler.ready_of_reserved,
      ``WeightedCallerHandler.step, ``callerBound, ``callerFits, ``callerMemory, ``callerReady, ``callerReservation, ``callerOracle,
      ``WeightedCaller.preserves, ``WeightedCaller.refines, ``WeightedCaller.start_postcondition,
      ``WeightedCaller.Postcondition.extraction_room, ``adaptiveRefines, ``adaptivePostcondition,
      ``WeightedCaller.execution_postcondition, ``WeightedCaller.observe_source, ``WeightedCaller.words, ``WeightedCaller.time,
      ``WeightedCaller.names, ``WeightedCaller.descriptionFits, ``WeightedCaller.resources,
      ``adaptiveTimeBound, ``adaptiveWordsBound, ``adaptiveFits, ``adaptiveMemory, ``adaptiveExecutedPostcondition] do
    for dependency in (← collectAxioms name) do
      unless dependency ∈ allowed do throwError "unexpected axiom {dependency} in {name}"

-- The extraction coefficient is applied after evaluating every original term.
private instance : Module (Word 16) (Ty.Value base (.atom true)) :=
  inferInstanceAs (Module (Word 16) (Word 16))
private def coefficientLayout : WeightedCoefficient.Layouts 16 Key (Word 16 × Word 16) (Word 16) (Word 16) :=
  ⟨accumulation.good, oops.input, by decide⟩
private def coefficientProximityLayout :
    WeightedCoefficient.Layouts 16 Key ((Fin 3 → Word 16) × Word 16) (Word 16) (Word 16) :=
  ⟨accumulation.good, proximity.input, by decide⟩
private def coefficientPairLayout :
    WeightedCoefficient.Layouts 16 Key (Word 16 × Word 16) (Word 16) (Word 16 × Word 16) :=
  ⟨accumulation.bad, oops.input, by decide⟩
private def coefficientCode := WeightedCoefficient.code (base := base) (key := .atom false) (val := .atom true)
  coefficientLayout ⟨0, trivial⟩ 4 (by decide) (by decide) oopsGenerator ⟨99, trivial⟩
  primitives comparison comparison_correct goodUpdate goodBuffers (by decide) uniformPort uniformDraw
private def coefficientProximityCode := WeightedCoefficient.code (base := base) (key := .atom false) (val := .atom true)
  coefficientProximityLayout ⟨0, trivial⟩ 4 (by decide) (by decide) proximityGenerator ⟨99, trivial⟩
  primitives comparison comparison_correct goodUpdate goodBuffers (by decide) uniformPort uniformDraw
private def coefficientPairCode := WeightedCoefficient.code (base := base) (key := .atom false)
  (val := .pair (.atom true) (.atom true)) coefficientPairLayout ⟨(0, 0), trivial, trivial⟩
  4 (by decide) (by decide) oopsGenerator ⟨(99, 98), trivial, trivial⟩
  primitives comparison comparison_correct badUpdate badBuffers (by decide) uniformPort uniformPairDraw
private def coefficientInput (coefficient accumulator : Word 16) (cache : List (Key × Word 16))
    (bounded : cache.length ≤ 8) : coefficientLayout.input.Value :=
  ⟨(message.val, coefficient, accumulator, cache), message.property, trivial,
    trivial, bounded, fun _ _ => ⟨⟨trivial, trivial⟩, trivial⟩⟩
private def coefficientTime := WeightedCoefficient.timeBudget (base := base) (key := .atom false) (val := .atom true)
  coefficientLayout 4 (by decide) (by decide) (OOPSTerms.timeBudget oops 6) 26
    (BLSAccumulate.goodTime accumulation.arithmetic 6 6)
private def coefficientWords := WeightedCoefficient.codeBudget (base := base) (key := .atom false) (val := .atom true)
  coefficientLayout 4 (by decide) (by decide) (OOPSTerms.codeBudget oops 27) 125
    (BLSAccumulate.goodCode accumulation.arithmetic 27 27)
private theorem coefficientBound : Interactive.TimeBoundOn
    (WeightedCoefficient.valid (base := base) (key := .atom false) (val := .atom true)
      coefficientLayout (generate := OOPSTerms.value))
    uniformPort .unit coefficientLayout.input.representation coefficientCode coefficientTime :=
  WeightedCoefficient.time_bound (base := base) (key := .atom false) (val := .atom true)
    coefficientLayout ⟨0, trivial⟩ 4 (by decide) (by decide) oopsGenerator ⟨99, trivial⟩
    primitives comparison comparison_correct goodUpdate goodBuffers (by decide) uniformPort uniformDraw uniformCorrect
    oopsBound (UniformSampling.time_bound (w := 16) 65535 (by decide) (by decide) 65535) goodBound
private theorem coefficientCodeBound : (coefficientCode.lower uniformPort).descriptionWords ≤ coefficientWords :=
  WeightedCoefficient.code_bound (base := base) (key := .atom false) (val := .atom true)
    coefficientLayout ⟨0, trivial⟩ 4 (by decide) (by decide) oopsGenerator ⟨99, trivial⟩
    primitives comparison comparison_correct goodUpdate goodBuffers (by decide) uniformPort uniformDraw
    oopsBound (UniformSampling.code_words (w := 16) 65535 (by decide) (by decide) 65535) goodBound
private theorem coefficientFits : (coefficientCode.lower uniformPort).DescriptionFits :=
  WeightedCoefficient.descriptionFits (base := base) (key := .atom false) (val := .atom true)
    coefficientLayout ⟨0, trivial⟩ 4 (by decide) (by decide) oopsGenerator ⟨99, trivial⟩
    primitives comparison comparison_correct goodUpdate goodBuffers (by decide) uniformPort uniformDraw
    (OOPSTerms.buffers oops trivial mul mulNames.buffers (by decide)) (by decide)
    (UniformSampling.descriptionFits (w := 16) 65535 (by decide) (by decide) 65535)
    (UniformSampling.names (w := 16) 65535 (by decide) (by decide) 65535) (by decide)
private theorem coefficientSource (value : coefficientLayout.input.Value)
    (admitted : WeightedCoefficient.valid (base := base) (key := .atom false) (val := .atom true)
      coefficientLayout (generate := OOPSTerms.value) value) :
    Subtype.val <$> WeightedCoefficient.denote (base := base) (key := .atom false) (val := .atom true)
      coefficientLayout ⟨0, trivial⟩ 4 (by decide) (by decide) oopsGenerator ⟨99, trivial⟩
      primitives comparison comparison_correct goodUpdate goodBuffers (by decide) uniformSource value =
      (fun answer => (value.val.2.2.1 + answer.1, answer.2)) <$>
        (simulateQ (BLS.LazyAGM.Reduction.privateListOracle (M := Key) (R := Word 16))
          (Model.LazyAGM.evalTerms ((OOPSTerms.value value.val.1).map
            fun term => (term.1, value.val.2.1 * term.2)))).run value.val.2.2.2 :=
  WeightedCoefficient.denote_source (base := base) (key := .atom false) (val := .atom true)
    coefficientLayout ⟨0, trivial⟩ 4 (by decide) (by decide) oopsGenerator ⟨99, trivial⟩
    primitives comparison comparison_correct goodUpdate goodBuffers (by decide)
    (fun _ => rfl) rfl uniformSource uniformLaw value admitted
private theorem coefficientMemory
    (tape : RandomTape 16) (value : coefficientLayout.input.Value)
    (admitted : WeightedCoefficient.valid (base := base) (key := .atom false) (val := .atom true)
      coefficientLayout (generate := OOPSTerms.value) value)
    (before : State 16) (holds : coefficientLayout.input.representation.Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers)
    (initialBuffers : before.SupportBound buffers) (finished : WordIO.Result 16)
    (reached : some finished ∈ support (coefficientCode.execute uniformPort .unit tape before)) :
    finished.time ≤ coefficientTime ∧
      ∃ execution : WordIO.Exec .unit tape (coefficientCode.lower uniformPort) before finished.state
          finished.trace finished.time finished.net finished.peak,
        ∀ between, execution.Visits between →
          ((coefficientCode.lower uniformPort).staticWords registers buffers : Int) +
            between.liveMem (max buffers (coefficientCode.lower uniformPort).memBound) ≤
              5 * coefficientWords + 20 + registers + 3 * buffers + before.liveMem buffers + coefficientTime := by
  obtain ⟨elapsed, _, _, _, execution, memory⟩ :=
    WeightedCoefficient.resources (base := base) (key := .atom false) (val := .atom true)
      coefficientLayout ⟨0, trivial⟩ 4 (by decide) (by decide) oopsGenerator ⟨99, trivial⟩
      primitives comparison comparison_correct goodUpdate goodBuffers (by decide) uniformPort uniformDraw
      uniformCorrect oopsBound
      (UniformSampling.time_bound (w := 16) 65535 (by decide) (by decide) 65535)
      (UniformSampling.code_words (w := 16) 65535 (by decide) (by decide) 65535)
      goodBound oopsNames (UniformSampling.names (w := 16) 65535 (by decide) (by decide) 65535) goodNames
      tape value admitted before holds registers buffers initialRegisters initialBuffers finished reached
  exact ⟨elapsed, execution, memory⟩

open Lean in
run_cmd do
  let samples : List (Word 16) := [2, 5, 7, 11]
  let fresh := samples.flatMap (fun sample => [65535, sample]) ++ [88]
  let trace := samples.flatMap (fun sample =>
    [WordIO.Event.output 65535, .invoke, .input 65535, .input sample])
  for coefficient in ([0, 5] : List (Word 16)) do
    for cache in ([⟨[], by decide⟩, ⟨entries, by decide⟩] : List {cache : List (Key × Word 16) // cache.length ≤ 8}) do
      let value := coefficientInput coefficient 9 cache.val cache.property
      match executeUniform coefficientLayout.input.representation coefficientLayout.state coefficientCode
          value (if cache.val.isEmpty then fresh else [88]) with
      | none => throwError "weighted coefficient execution failed"
      | some (answer, framed, capacity, register, tape, scratch, events, remaining, elapsed) =>
        unless answer == (9 + coefficient * 377, entries) && framed == #[77] && capacity == 4 &&
            register == 91 && tape == 9 && scratch && remaining == [88] && elapsed ≤ coefficientTime &&
            events == (if cache.val.isEmpty then trace else []) do
          throwError "coefficient scaling changed reads, cache, old accumulator, frame or time bound"
  -- The second occurrence receives a new coefficient but reuses the first result's cache.
  match executeUniform coefficientLayout.input.representation coefficientLayout.state coefficientCode
      (coefficientInput 5 9 [] (by decide)) fresh with
  | none => throwError "first coefficient occurrence failed"
  | some (first, _, _, _, _, _, _, _, _) =>
    if bounded : first.2.length ≤ 8 then
      match executeUniform coefficientLayout.input.representation coefficientLayout.state coefficientCode
          (coefficientInput 7 first.1 first.2 bounded) [88] with
      | none => throwError "second coefficient occurrence failed"
      | some (answer, _, _, _, _, _, events, remaining, elapsed) =>
        unless answer == (4533, entries) && events.isEmpty && remaining == [88] && elapsed ≤ coefficientTime do
          throwError "repeated message occurrence lost positional coefficient or cache sharing"
    else throwError "first coefficient occurrence exceeded its cache capacity"
  let pvalue : coefficientProximityLayout.input.Value :=
    ⟨((vector 3 9 27).val, 5, 9, []), (vector 3 9 27).property, trivial,
      trivial, by decide, by simp⟩
  match executeUniform coefficientProximityLayout.input.representation coefficientProximityLayout.state
      coefficientProximityCode pvalue fresh with
  | none => throwError "Proximity coefficient execution failed"
  | some (answer, framed, capacity, register, tape, scratch, events, remaining, _) =>
    unless answer == (1894, entries) && framed == #[77] && capacity == 4 &&
        register == 91 && tape == 9 && scratch && events == trace && remaining == [88] do
      throwError "Proximity coefficient changed vector terms, sampling or retained frame"
  let pairSamples : List (Word 16) := [2, 3, 5, 7, 11, 13, 17, 19]
  let pairTrace := pairSamples.flatMap (fun sample =>
    [WordIO.Event.output 65535, .invoke, .input 65535, .input sample])
  for coefficient in ([0, 5] : List (Word 16)) do
    let value : coefficientPairLayout.input.Value :=
      ⟨(message.val, coefficient, (9, 10), []), message.property, trivial,
        ⟨trivial, trivial⟩, by change (0 : Nat) ≤ 8; decide, by simp⟩
    match executeUniform coefficientPairLayout.input.representation coefficientPairLayout.state coefficientPairCode
        value (pairSamples.flatMap (fun sample => [65535, sample]) ++ [88]) with
    | none => throwError "pair coefficient execution failed"
    | some (answer, framed, capacity, register, tape, scratch, events, remaining, _) =>
      unless answer == ((9 + coefficient * 575, 10 + coefficient * 654),
          [((3, 42), (17, 19)), ((2, 42), (11, 13)), ((1, 42), (5, 7)), ((0, 42), (2, 3))]) &&
          framed == #[77] && capacity == 4 && register == 91 && tape == 9 && scratch &&
          events == pairTrace && remaining == [88] do
        throwError "pair coefficient changed coordinate scaling, zero reads, cache or frame"
  let transcript : List ((Word 16 × Word 16) × Word 16) := [(message.val, 17), (message.val, 13)]
  let shortRows := WeightedAGM.Batching.chronologicalRows transcript [5]
  let longRows := WeightedAGM.Batching.chronologicalRows transcript [5, 7, 11]
  unless shortRows.map Prod.snd == [5, 0] && longRows.map Prod.snd == [5, 7] &&
      shortRows.map (fun row => row.1.2) == [13, 17] &&
      WeightedAGM.Batching.reads (OOPSTerms.value (degree := 3)) shortRows == 8 &&
      (WeightedAGM.Batching.expanded (OOPSTerms.value (degree := 3)) shortRows).length == 8 do
    throwError "chronological batching dropped repeated or zero-coefficient occurrences"
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``WeightedAGM.Batching.evalTerms_scale, ``WeightedAGM.Batching.evalTerms_append,
      ``WeightedAGM.Batching.execute_source, ``WeightedAGM.Batching.execute_signedTerms,
      ``WeightedAGM.Batching.cached_signedTerms, ``WeightedAGM.Batching.cache_growth,
      ``WeightedAGM.Batching.chronological_reads_bound, ``WeightedAGM.Batching.remaining_room,
      ``WeightedCoefficient.refines, ``WeightedCoefficient.cache_growth, ``WeightedCoefficient.denote_source,
      ``WeightedCoefficient.time_bound, ``WeightedCoefficient.code_bound, ``WeightedCoefficient.names,
      ``WeightedCoefficient.descriptionFits, ``WeightedCoefficient.resources,
      ``coefficientBound, ``coefficientCodeBound, ``coefficientFits, ``coefficientSource, ``coefficientMemory] do
    for dependency in (← collectAxioms name) do
      unless dependency ∈ allowed do throwError "unexpected axiom {dependency} in {name}"

private def extractionRows : WeightedToken.Layouts 16 Key (Word 16 × Word 16) (Word 16) (Word 16) (Word 16) :=
  ⟨coefficientLayout, scalar, by decide⟩
private def extractionLayout : WeightedExtraction.Layouts 16 Key (Word 16 × Word 16) (Word 16) (Word 16) (Word 16) where
  rows := extractionRows
  capacity := 3
  coefficients := 4
  terms := 4
  termCountFits := by decide
  termStorageFits := by decide
  counterFits := by decide
  coefficientCountFits := by decide
  storageFits := by decide
private def extractionProximityRows :
    WeightedToken.Layouts 16 Key ((Fin 3 → Word 16) × Word 16) (Word 16) (Word 16) (Word 16) :=
  ⟨coefficientProximityLayout, scalar, by decide⟩
private def extractionProximityLayout :
    WeightedExtraction.Layouts 16 Key ((Fin 3 → Word 16) × Word 16) (Word 16) (Word 16) (Word 16) :=
  ⟨extractionProximityRows, 3, 4, 4, by decide, by decide, by decide, by decide, by decide⟩
private def extractionPairRows :
    WeightedToken.Layouts 16 Key (Word 16 × Word 16) (Word 16) (Word 16) (Word 16 × Word 16) :=
  ⟨coefficientPairLayout, scalar, by decide⟩
private def extractionPairLayout :
    WeightedExtraction.Layouts 16 Key (Word 16 × Word 16) (Word 16) (Word 16) (Word 16 × Word 16) :=
  ⟨extractionPairRows, 3, 4, 4, by decide, by decide, by decide, by decide, by decide⟩
private def extractionCode := WeightedExtraction.code (base := base) (key := .atom false) (val := .atom true)
  extractionLayout ⟨0, trivial⟩ ⟨0, trivial⟩ ⟨9, trivial⟩ ⟨99, trivial⟩ oopsGenerator
  primitives comparison comparison_correct goodUpdate goodBuffers (by decide) uniformPort uniformDraw
private def extractionProximityCode := WeightedExtraction.code (base := base) (key := .atom false) (val := .atom true)
  extractionProximityLayout ⟨0, trivial⟩ ⟨0, trivial⟩ ⟨9, trivial⟩ ⟨99, trivial⟩ proximityGenerator
  primitives comparison comparison_correct goodUpdate goodBuffers (by decide) uniformPort uniformDraw
private def extractionPairCode := WeightedExtraction.code (base := base) (key := .atom false) (val := .pair (.atom true) (.atom true))
  extractionPairLayout ⟨0, trivial⟩ ⟨(0, 0), trivial, trivial⟩ ⟨(9, 10), trivial, trivial⟩ ⟨(99, 98), trivial, trivial⟩ oopsGenerator
  primitives comparison comparison_correct badUpdate badBuffers (by decide) uniformPort uniformPairDraw
private def extractionInput (transcript : List ((Word 16 × Word 16) × Word 16)) (coefficients : List (Word 16))
    (cache : List (Key × Word 16)) (tokens : transcript.length ≤ 3) (scalars : coefficients.length ≤ 4)
    (cacheBound : cache.length ≤ 8) : extractionLayout.input.Value :=
  ⟨((transcript, coefficients), cache),
    ⟨⟨tokens, fun _ _ => ⟨⟨trivial, trivial⟩, trivial⟩⟩, scalars, fun _ _ => trivial⟩,
    cacheBound, fun _ _ => ⟨⟨trivial, trivial⟩, trivial⟩⟩
private def extractionTime := WeightedExtraction.timeBudget (base := base) (key := .atom false) (val := .atom true)
  extractionLayout (OOPSTerms.timeBudget oops 6) 26 (BLSAccumulate.goodTime accumulation.arithmetic 6 6)
private def extractionWords := WeightedExtraction.codeBudget (base := base) (key := .atom false) (val := .atom true)
  extractionLayout (OOPSTerms.codeBudget oops 27) 125 (BLSAccumulate.goodCode accumulation.arithmetic 27 27)
private theorem extractionBound : Interactive.TimeBoundOn extractionLayout.ready uniformPort .unit
    extractionLayout.input.representation extractionCode extractionTime :=
  WeightedExtraction.time_bound (base := base) (key := .atom false) (val := .atom true)
    extractionLayout ⟨0, trivial⟩ ⟨0, trivial⟩ ⟨9, trivial⟩ ⟨99, trivial⟩ oopsGenerator
    primitives comparison comparison_correct goodUpdate goodBuffers (by decide) uniformPort uniformCorrect oopsBound
    (UniformSampling.time_bound (w := 16) 65535 (by decide) (by decide) 65535) goodBound
private theorem extractionFits : (extractionCode.lower uniformPort).DescriptionFits :=
  WeightedExtraction.descriptionFits (base := base) (key := .atom false) (val := .atom true)
    extractionLayout ⟨0, trivial⟩ ⟨0, trivial⟩ ⟨9, trivial⟩ ⟨99, trivial⟩ oopsGenerator
    primitives comparison comparison_correct goodUpdate goodBuffers (by decide) uniformPort uniformDraw
    (OOPSTerms.buffers oops trivial mul mulNames.buffers (by decide)) (by decide)
    (UniformSampling.descriptionFits (w := 16) 65535 (by decide) (by decide) 65535)
    (UniformSampling.names (w := 16) 65535 (by decide) (by decide) 65535) (by decide) (by decide)
private theorem extractionOracle (tape : RandomTape 16) (value : extractionLayout.input.Value)
    (admitted : extractionLayout.ready value) (before : State 16) (holds : extractionLayout.input.representation.Holds value before) :
    (fun result => (fun answer => (answer.val.1, answer.val.2.map (Prod.map Prod.swap id))) <$>
        Interactive.observe extractionLayout.rows.state.representation result) <$>
      extractionCode.execute uniformPort .unit tape before =
      some <$> ((fun answer => (9 + answer.1, answer.2)) <$>
        (simulateQ (BLS.LazyAGM.Reduction.privateListOracle (M := Word 16 × Fin 4) (R := Word 16))
          (Model.LazyAGM.evalTerms (Model.LazyAGM.WeightedReduction.signedTerms (OOPS.LazyAGM.terms 3)
            value.val.1.2 value.val.1.1.reverse))).run (value.val.2.map (Prod.map Prod.swap id))) :=
  WeightedExtraction.observe_equiv (base := base) (key := .atom false) (val := .atom true)
    extractionLayout ⟨0, trivial⟩ ⟨0, trivial⟩ ⟨9, trivial⟩ ⟨99, trivial⟩ oopsGenerator
    primitives comparison comparison_correct goodUpdate goodBuffers (by decide) (fun _ => rfl) rfl rfl
    uniformSource uniformLaw (Equiv.prodComm (Word 16) (Fin 4)) (OOPS.LazyAGM.terms 3) (OOPSTerms.source 3)
    uniformPort uniformDraw uniformCorrect tape value admitted before holds
private theorem extractionMemory (tape : RandomTape 16) (value : extractionLayout.input.Value)
    (admitted : extractionLayout.ready value) (before : State 16) (holds : extractionLayout.input.representation.Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result 16) (reached : some finished ∈ support (extractionCode.execute uniformPort .unit tape before)) :
    finished.time ≤ extractionTime ∧
      ∃ execution : WordIO.Exec .unit tape (extractionCode.lower uniformPort) before finished.state
          finished.trace finished.time finished.net finished.peak,
        ∀ between, execution.Visits between →
          ((extractionCode.lower uniformPort).staticWords registers buffers : Int) +
            between.liveMem (max buffers (extractionCode.lower uniformPort).memBound) ≤
              5 * extractionWords + 20 + registers + 3 * buffers + before.liveMem buffers + extractionTime := by
  obtain ⟨elapsed, _, _, _, execution, memory⟩ :=
    WeightedExtraction.resources (base := base) (key := .atom false) (val := .atom true)
      extractionLayout ⟨0, trivial⟩ ⟨0, trivial⟩ ⟨9, trivial⟩ ⟨99, trivial⟩ oopsGenerator
      primitives comparison comparison_correct goodUpdate goodBuffers (by decide) uniformPort uniformDraw uniformCorrect
      oopsBound (UniformSampling.time_bound (w := 16) 65535 (by decide) (by decide) 65535)
      (UniformSampling.code_words (w := 16) 65535 (by decide) (by decide) 65535) goodBound oopsNames
      (UniformSampling.names (w := 16) 65535 (by decide) (by decide) 65535) goodNames
      tape value admitted before holds registers buffers initialRegisters initialBuffers finished reached
  exact ⟨elapsed, execution, fun between visited => (memory between visited).2.2.2⟩

open Lean in
run_cmd do
  let firstSamples : List (Word 16) := [2, 5, 7, 11]
  let secondSamples : List (Word 16) := [3, 7, 11, 13]
  let allSamples := firstSamples ++ secondSamples
  let replies := allSamples.flatMap (fun sample => [65535, sample]) ++ [88]
  let trace := allSamples.flatMap (fun sample => [WordIO.Event.output 65535, .invoke, .input 65535, .input sample])
  let secondCache : List (Key × Word 16) := [((3, 43), 13), ((2, 43), 11), ((1, 43), 7), ((0, 43), 3)]
  let coefficients : List {values : List (Word 16) // values.length ≤ 4} :=
    [⟨[5, 7], by decide⟩, ⟨[5], by decide⟩, ⟨[0, 0], by decide⟩, ⟨[5, 7, 99], by decide⟩]
  for cs in coefficients do
    let value := extractionInput [((2, 43), 17), (message.val, 13)] cs.val [] (by decide) cs.property (by decide)
    unless decide (extractionLayout.ready value) do
      throwError "extraction reserved padded capacity instead of actual token count"
    match executeUniform extractionLayout.input.representation extractionLayout.rows.state extractionCode value replies with
    | none => throwError "complete weighted transcript extraction failed"
    | some (answer, framed, capacity, register, tape, scratch, events, remaining, elapsed) =>
      let expected := 9 + (cs.val[0]?).getD 0 * 377 + (cs.val[1]?).getD 0 * 165
      unless answer == (expected, secondCache ++ entries) && framed == #[77] && capacity == 4 &&
          register == 91 && tape == 9 && scratch && events == trace && remaining == [88] && elapsed ≤ extractionTime do
        throwError "weighted extraction lost chronological coefficients, zero reads, cache order, frame or budget"
  let firstReplies := firstSamples.flatMap (fun sample => [65535, sample]) ++ [88]
  let firstTrace := firstSamples.flatMap (fun sample => [WordIO.Event.output 65535, .invoke, .input 65535, .input sample])
  let repeated := extractionInput [(message.val, 17), (message.val, 13)] [5, 7] [] (by decide) (by decide) (by decide)
  match executeUniform extractionLayout.input.representation extractionLayout.rows.state extractionCode repeated firstReplies with
  | none => throwError "repeated-message transcript extraction failed"
  | some (answer, framed, capacity, register, tape, scratch, events, remaining, elapsed) =>
    unless answer == (4533, entries) && framed == #[77] && capacity == 4 && register == 91 &&
        tape == 9 && scratch && events == firstTrace && remaining == [88] && elapsed ≤ extractionTime do
      throwError "repeated-message extraction resampled or merged occurrence coefficients"
  let cases : List (extractionLayout.input.Value × Word 16) :=
    [(extractionInput [] [5] entries (by decide) (by decide) (by decide), 9),
     (extractionInput [(message.val, 13)] [5] entries (by decide) (by decide) (by decide), 1894)]
  for (value, expected) in cases do
    match executeUniform extractionLayout.input.representation extractionLayout.rows.state extractionCode value [88] with
    | none => throwError "empty or cached extraction failed"
    | some (answer, framed, capacity, register, tape, scratch, events, remaining, elapsed) =>
      unless answer == (expected, entries) && framed == #[77] && capacity == 4 && register == 91 &&
          tape == 9 && scratch && events.isEmpty && remaining == [88] && elapsed ≤ extractionTime do
        throwError "empty or cached extraction changed cache, consumed samples or lost framing"
  let oversized := extractionInput [(message.val, 17), (message.val, 13)] [5, 7] entries
    (by decide) (by decide) (by decide)
  unless !(decide (extractionLayout.ready oversized)) do
    throwError "weighted extraction admission ignored its cache reservation"
  let pvalue : extractionProximityLayout.input.Value :=
    ⟨(([( ((vector 2 4 8).val.1, 43), 17), ((vector 3 9 27).val, 13)], [5, 7]), []),
      ⟨⟨by decide, fun _ _ => ⟨⟨(fun _ => trivial), trivial⟩, trivial⟩⟩,
        by decide, fun _ _ => trivial⟩, by decide, by simp⟩
  match executeUniform extractionProximityLayout.input.representation extractionProximityLayout.rows.state
      extractionProximityCode pvalue replies with
  | none => throwError "complete Proximity transcript extraction failed"
  | some (answer, framed, capacity, register, tape, scratch, events, remaining, _) =>
    unless answer == (3049, secondCache ++ entries) && framed == #[77] && capacity == 4 &&
        register == 91 && tape == 9 && scratch && events == trace && remaining == [88] do
      throwError "Proximity transcript extraction changed vector terms, chronology or state"
  let pairSamples : List (Word 16) := [2, 3, 5, 7, 11, 13, 17, 19]
  let pairTrace := pairSamples.flatMap (fun sample => [WordIO.Event.output 65535, .invoke, .input 65535, .input sample])
  let pairValue : extractionPairLayout.input.Value :=
    ⟨(([(message.val, 17), (message.val, 13)], [5, 7]), []),
      ⟨⟨by decide, fun _ _ => ⟨⟨trivial, trivial⟩, trivial⟩⟩, by decide, fun _ _ => trivial⟩, by decide, by simp⟩
  match executeUniform extractionPairLayout.input.representation extractionPairLayout.rows.state extractionPairCode pairValue
      (pairSamples.flatMap (fun sample => [65535, sample]) ++ [88]) with
  | none => throwError "complete pair transcript extraction failed"
  | some (answer, framed, capacity, register, tape, scratch, events, remaining, _) =>
    unless answer == ((6909, 7858),
        [((3, 42), (17, 19)), ((2, 42), (11, 13)), ((1, 42), (5, 7)), ((0, 42), (2, 3))]) &&
        framed == #[77] && capacity == 4 && register == 91 && tape == 9 && scratch &&
        events == pairTrace && remaining == [88] do
      throwError "pair transcript extraction changed coordinate sums, shared cache or retained frame"
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``WeightedToken.refines, ``WeightedToken.ready_of_room, ``WeightedToken.preserves,
      ``WeightedToken.time_bound, ``WeightedToken.code_bound, ``WeightedToken.buffers,
      ``WeightedTokenFold.refines, ``WeightedTokenFold.time_bound, ``WeightedTokenFold.code_bound,
      ``WeightedTokenFold.descriptionFits, ``WeightedTokenFold.listCache, ``WeightedTokenFold.cache_growth,
      ``WeightedExtraction.prepare_bounded, ``WeightedExtraction.refines, ``WeightedExtraction.time_bound,
      ``WeightedExtraction.code_bound, ``WeightedExtraction.denote_source, ``WeightedExtraction.denote_encoded,
      ``WeightedExtraction.denote_equiv, ``WeightedExtraction.observe_equiv, ``WeightedExtraction.cache_growth,
      ``WeightedExtraction.remaining_room, ``WeightedExtraction.descriptionFits, ``WeightedExtraction.resources,
      ``extractionBound, ``extractionFits, ``extractionOracle, ``extractionMemory] do
    for dependency in (← collectAxioms name) do
      unless dependency ∈ allowed do throwError "unexpected axiom {dependency} in {name}"

-- The target stage uses the constructed subtraction/negation/division routines.
-- These word fixtures test execution, without claiming field laws for Word 16.
private def sub := binary .sub
private def divide := binary .udiv
private def scalarZero : Implementation .unit scalar scalar (fun _ => 0) :=
  Implementation.constant scalar scalar ⟨0, trivial⟩ accumulation.cache.wordFits
private def negArgs : Implementation .unit scalar accumulation.arithmetic.pair (fun value => (0, value)) :=
  scalarZero.pair (Implementation.identity scalar (by decide)) (by decide) accumulation.cache.wordFits
    (by decide) (by decide) (by decide) (by decide) accumulation.arithmetic.pair.representation.fits
private def negate : Implementation .unit scalar scalar Neg.neg :=
  (negArgs.then sub).castFunction (by funext value; exact BitVec.zero_sub value)
private theorem subBound : sub.BoundedBy 6 27 := ⟨fun _ => le_rfl, by decide⟩
private theorem divBound : divide.BoundedBy 6 27 := ⟨fun _ => le_rfl, by decide⟩
private theorem negBound : negate.BoundedBy 118 631 := by
  have zeroBound := Implementation.constant_bounded scalar scalar ⟨0, trivial⟩ accumulation.cache.wordFits
  have paired : negArgs.BoundedBy 112 603 := by
    apply (Implementation.pair_boundedBy scalarZero (Implementation.identity scalar (by decide))
      accumulation.cache.wordFits (by decide) (by decide) (by decide) (by decide)
      accumulation.arithmetic.pair.representation.fits
      zeroBound (Implementation.identity_boundedBy scalar (by decide))).mono <;> decide
  apply ((paired.then subBound).castFunction _).mono <;> decide
private theorem subNames : NamesBound sub.program.code 3 := ⟨by decide, by decide⟩
private theorem divNames : NamesBound divide.program.code 3 := ⟨by decide, by decide⟩
private theorem negNames : NamesBound negate.program.code 3 := ⟨by decide, by decide⟩
private def goodExtract := BLSExtractArithmetic.good accumulation.arithmetic sub subNames.buffers (by decide) divide
private def badExtract := BLSExtractArithmetic.bad accumulation.arithmetic sub subNames.buffers (by decide)
  negate negNames.buffers divide
private theorem goodExtractBuffers : goodExtract.program.code.memBound ≤ 4 :=
  BLSExtractArithmetic.good_buffers accumulation.arithmetic sub subNames.buffers (by decide) divide divNames.buffers
private theorem badExtractBuffers : badExtract.program.code.memBound ≤ 4 :=
  BLSExtractArithmetic.bad_buffers accumulation.arithmetic sub subNames.buffers (by decide)
    negate negNames.buffers divide divNames.buffers
private theorem goodExtractBound : goodExtract.BoundedBy
    (BLSExtractArithmetic.goodTime accumulation.arithmetic 6 6)
    (BLSExtractArithmetic.goodCode accumulation.arithmetic 27 27) :=
  BLSExtractArithmetic.good_bounded accumulation.arithmetic sub subBound subNames.buffers (by decide) divide divBound
private theorem badExtractBound : badExtract.BoundedBy
    (BLSExtractArithmetic.badTime accumulation.arithmetic 6 118 6)
    (BLSExtractArithmetic.badCode accumulation.arithmetic 27 631 27) :=
  BLSExtractArithmetic.bad_bounded accumulation.arithmetic sub subBound subNames.buffers (by decide)
    negate negBound negNames.buffers divide divBound
private theorem goodExtractNames : NamesAccounted goodExtract.program.code 3 :=
  BLSExtractArithmetic.good_names accumulation.arithmetic 3 sub subNames.accounted subNames.buffers
    (by decide) divide divNames.accounted
private def targetCode := WeightedTarget.code (base := base) (key := .atom false) (val := .atom true)
  coefficientLayout ⟨0, trivial⟩ 4 (by decide) (by decide) oopsGenerator ⟨99, trivial⟩
  primitives comparison comparison_correct goodUpdate goodBuffers (by decide)
  goodExtract goodExtractBuffers (by decide) uniformPort uniformDraw
private def targetProximityCode := WeightedTarget.code (base := base) (key := .atom false) (val := .atom true)
  coefficientProximityLayout ⟨0, trivial⟩ 4 (by decide) (by decide) proximityGenerator ⟨99, trivial⟩
  primitives comparison comparison_correct goodUpdate goodBuffers (by decide)
  goodExtract goodExtractBuffers (by decide) uniformPort uniformDraw
private def targetPairCode := WeightedTarget.code (base := base) (key := .atom false)
  (val := .pair (.atom true) (.atom true)) coefficientPairLayout ⟨(0, 0), trivial, trivial⟩
  4 (by decide) (by decide) oopsGenerator ⟨(99, 98), trivial, trivial⟩
  primitives comparison comparison_correct badUpdate badBuffers (by decide)
  badExtract badExtractBuffers (by decide) uniformPort uniformPairDraw
private def targetTime := WeightedTarget.timeBudget (base := base) (key := .atom false) (val := .atom true)
  coefficientLayout 4 (by decide) (by decide) (OOPSTerms.timeBudget oops 6) 26
    (BLSAccumulate.goodTime accumulation.arithmetic 6 6)
    (BLSExtractArithmetic.goodTime accumulation.arithmetic 6 6)
private def targetWords := WeightedTarget.codeBudget (base := base) (key := .atom false) (val := .atom true)
  coefficientLayout 4 (by decide) (by decide) (OOPSTerms.codeBudget oops 27) 125
    (BLSAccumulate.goodCode accumulation.arithmetic 27 27)
    (BLSExtractArithmetic.goodCode accumulation.arithmetic 27 27)
private def targetPairTime := WeightedTarget.timeBudget (base := base) (key := .atom false)
  (val := .pair (.atom true) (.atom true)) coefficientPairLayout 4 (by decide) (by decide)
    (OOPSTerms.timeBudget oops 6) (PairSampling.timeBudget scalar scalar 26 26)
    (BLSAccumulate.badTime accumulation.arithmetic 6 6)
    (BLSExtractArithmetic.badTime accumulation.arithmetic 6 118 6)
private theorem targetBound : Interactive.TimeBoundOn
    (WeightedCoefficient.valid (base := base) (key := .atom false) (val := .atom true)
      coefficientLayout (generate := OOPSTerms.value))
    uniformPort .unit coefficientLayout.input.representation targetCode targetTime :=
  WeightedTarget.time_bound (base := base) (key := .atom false) (val := .atom true)
    coefficientLayout ⟨0, trivial⟩ 4 (by decide) (by decide) oopsGenerator ⟨99, trivial⟩
    primitives comparison comparison_correct goodUpdate goodBuffers (by decide)
    goodExtract goodExtractBuffers (by decide) uniformPort uniformDraw uniformCorrect
    oopsBound (UniformSampling.time_bound (w := 16) 65535 (by decide) (by decide) 65535) goodBound goodExtractBound
private theorem targetPairBound : Interactive.TimeBoundOn
    (WeightedCoefficient.valid (base := base) (key := .atom false) (val := .pair (.atom true) (.atom true))
      coefficientPairLayout (generate := OOPSTerms.value))
    uniformPort .unit coefficientPairLayout.input.representation targetPairCode targetPairTime :=
  WeightedTarget.time_bound (base := base) (key := .atom false) (val := .pair (.atom true) (.atom true))
    coefficientPairLayout ⟨(0, 0), trivial, trivial⟩ 4 (by decide) (by decide) oopsGenerator ⟨(99, 98), trivial, trivial⟩
    primitives comparison comparison_correct badUpdate badBuffers (by decide)
    badExtract badExtractBuffers (by decide) uniformPort uniformPairDraw uniformPairCorrect oopsBound
    (PairSampling.time_bound uniformCorrect uniformCorrect
      (UniformSampling.time_bound (w := 16) 65535 (by decide) (by decide) 65535)
      (UniformSampling.time_bound (w := 16) 65535 (by decide) (by decide) 65535))
    (BLSAccumulate.bad_bounded accumulation.arithmetic mul add mulBound addBound mulNames.buffers (by decide) addNames.buffers)
    badExtractBound
private theorem targetFits : (targetCode.lower uniformPort).DescriptionFits :=
  WeightedTarget.descriptionFits (base := base) (key := .atom false) (val := .atom true)
    coefficientLayout ⟨0, trivial⟩ 4 (by decide) (by decide) oopsGenerator ⟨99, trivial⟩
    primitives comparison comparison_correct goodUpdate goodBuffers (by decide)
    goodExtract goodExtractBuffers (by decide) uniformPort uniformDraw
    (OOPSTerms.buffers oops trivial mul mulNames.buffers (by decide)) (by decide)
    (UniformSampling.descriptionFits (w := 16) 65535 (by decide) (by decide) 65535)
    (UniformSampling.names (w := 16) 65535 (by decide) (by decide) 65535) (by decide)
private theorem targetOracle (tape : RandomTape 16) (value : coefficientLayout.input.Value)
    (admitted : WeightedCoefficient.valid (base := base) (key := .atom false) (val := .atom true)
      coefficientLayout (generate := OOPSTerms.value) value)
    (before : State 16) (holds : coefficientLayout.input.representation.Holds value before) :
    (fun result => (fun answer => (answer.val.1, answer.val.2.map (Prod.map Prod.swap id))) <$>
        Interactive.observe (WeightedTarget.output coefficientLayout).representation result) <$>
      targetCode.execute uniformPort .unit tape before =
      some <$> ((fun answer => (value.val.2.1 / (answer.1 - value.val.2.2.1), answer.2)) <$>
        (simulateQ (BLS.LazyAGM.Reduction.privateListOracle (M := Word 16 × Fin 4) (R := Word 16))
          (Model.LazyAGM.evalTerms (OOPS.LazyAGM.terms 3 value.val.1))).run
            (value.val.2.2.2.map (Prod.map Prod.swap id))) :=
  WeightedTarget.observe_equiv (base := base) (key := .atom false) (val := .atom true)
    coefficientLayout ⟨0, trivial⟩ 4 (by decide) (by decide) oopsGenerator ⟨99, trivial⟩
    primitives comparison comparison_correct goodUpdate goodBuffers (by decide)
    goodExtract goodExtractBuffers (by decide) (fun _ => rfl) rfl uniformSource uniformLaw
    (Equiv.prodComm (Word 16) (Fin 4)) (OOPS.LazyAGM.terms 3) (OOPSTerms.source 3)
    uniformPort uniformDraw uniformCorrect tape value admitted before holds
private theorem targetMemory (tape : RandomTape 16) (value : coefficientLayout.input.Value)
    (admitted : WeightedCoefficient.valid (base := base) (key := .atom false) (val := .atom true)
      coefficientLayout (generate := OOPSTerms.value) value)
    (before : State 16) (holds : coefficientLayout.input.representation.Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers)
    (initialBuffers : before.SupportBound buffers) (finished : WordIO.Result 16)
    (reached : some finished ∈ support (targetCode.execute uniformPort .unit tape before)) :
    finished.time ≤ targetTime ∧
      ∃ execution : WordIO.Exec .unit tape (targetCode.lower uniformPort) before finished.state
          finished.trace finished.time finished.net finished.peak,
        ∀ between, execution.Visits between →
          ((targetCode.lower uniformPort).staticWords registers buffers : Int) +
            between.liveMem (max buffers (targetCode.lower uniformPort).memBound) ≤
              5 * targetWords + 20 + registers + 3 * buffers + before.liveMem buffers + targetTime := by
  obtain ⟨elapsed, _, _, _, execution, memory⟩ :=
    WeightedTarget.resources (base := base) (key := .atom false) (val := .atom true)
      coefficientLayout ⟨0, trivial⟩ 4 (by decide) (by decide) oopsGenerator ⟨99, trivial⟩
      primitives comparison comparison_correct goodUpdate goodBuffers (by decide)
      goodExtract goodExtractBuffers (by decide) uniformPort uniformDraw uniformCorrect oopsBound
      (UniformSampling.time_bound (w := 16) 65535 (by decide) (by decide) 65535)
      (UniformSampling.code_words (w := 16) 65535 (by decide) (by decide) 65535)
      goodBound goodExtractBound oopsNames
      (UniformSampling.names (w := 16) 65535 (by decide) (by decide) 65535) goodNames goodExtractNames
      tape value admitted before holds registers buffers initialRegisters initialBuffers finished reached
  exact ⟨elapsed, execution, memory⟩

open Lean in
run_cmd do
  let samples : List (Word 16) := [2, 5, 7, 11]
  for (numerator, signatures, expected) in
      ([(740, 7, 2), (0, 7, 0), (740, 377, 0)] : List (Word 16 × Word 16 × Word 16)) do
    for cache in ([⟨[], by decide⟩, ⟨entries, by decide⟩] : List {cache : List (Key × Word 16) // cache.length ≤ 8}) do
      let value := coefficientInput numerator signatures cache.val cache.property
      let needed := if cache.val.isEmpty then samples else []
      let trace := needed.flatMap (fun sample => [WordIO.Event.output 65535, .invoke, .input 65535, .input sample])
      match executeUniform coefficientLayout.input.representation (WeightedTarget.output coefficientLayout)
          targetCode value (needed.flatMap (fun sample => [65535, sample]) ++ [88]) with
      | none => throwError "weighted final target execution failed"
      | some (answer, framed, capacity, register, tape, scratch, events, remaining, elapsed) =>
        unless answer == (expected, entries) && framed == #[77] && capacity == 4 && register == 91 &&
            tape == 9 && scratch && events == trace && remaining == [88] && elapsed ≤ targetTime do
          throwError "weighted final target changed arithmetic, cache, sampling, framing or cost: numerator={numerator.toNat}, signatures={signatures.toNat}, expected={expected.toNat}, actual={answer.1.toNat}"
  let unrelated : List (Key × Word 16) := [((0, 77), 123)]
  let mixed := coefficientInput 740 7 (⟨(0, 42), 2⟩ :: unrelated) (by decide)
  let needed : List (Word 16) := [5, 7, 11]
  match executeUniform coefficientLayout.input.representation (WeightedTarget.output coefficientLayout)
      targetCode mixed (needed.flatMap (fun sample => [65535, sample]) ++ [88]) with
  | none => throwError "partly cached final target failed"
  | some (answer, _, _, _, _, scratch, events, remaining, elapsed) =>
    let trace := needed.flatMap (fun sample => [WordIO.Event.output 65535, .invoke, .input 65535, .input sample])
    unless answer == (2, entries ++ unrelated) && scratch && events == trace && remaining == [88] &&
        elapsed ≤ targetTime do
      throwError "final target lost unrelated cache entries or resampled a hit"
  for (message, expected) in [(vector 3 9 27, (2 : Word 16)), (vector 0 0 0, 370)] do
    let value : coefficientProximityLayout.input.Value :=
      ⟨(message.val, 740, (if expected == 2 then 7 else 0), []),
        message.property, trivial, trivial, by change (0 : Nat) ≤ 8; decide, by simp⟩
    match executeUniform coefficientProximityLayout.input.representation (WeightedTarget.output coefficientProximityLayout)
        targetProximityCode value (samples.flatMap (fun sample => [65535, sample]) ++ [88]) with
    | none => throwError "Proximity final target failed"
    | some (answer, framed, capacity, register, tape, scratch, events, remaining, _) =>
      let trace := samples.flatMap (fun sample => [WordIO.Event.output 65535, .invoke, .input 65535, .input sample])
      unless answer == (expected, entries) && framed == #[77] && capacity == 4 && register == 91 &&
          tape == 9 && scratch && events == trace && remaining == [88] do
        throwError "Proximity target dropped zero-coefficient reads or changed the scalar result"
  let pairSamples : List (Word 16) := [2, 3, 5, 7, 11, 13, 17, 19]
  let pairEntries : List (Key × (Word 16 × Word 16)) :=
    [((3, 42), (17, 19)), ((2, 42), (11, 13)), ((1, 42), (5, 7)), ((0, 42), (2, 3))]
  for beta in ([0, 999] : List (Word 16)) do
    for cache in ([⟨[], by decide⟩, ⟨pairEntries, by decide⟩] :
        List {cache : List (Key × (Word 16 × Word 16)) // cache.length ≤ 8}) do
      let value : coefficientPairLayout.input.Value :=
        ⟨(message.val, beta, (573, 700), cache.val), message.property, trivial, ⟨trivial, trivial⟩,
          cache.property, fun _ _ => ⟨⟨trivial, trivial⟩, trivial, trivial⟩⟩
      let needed := if cache.val.isEmpty then pairSamples else []
      let trace := needed.flatMap (fun sample => [WordIO.Event.output 65535, .invoke, .input 65535, .input sample])
      match executeUniform coefficientPairLayout.input.representation (WeightedTarget.output coefficientPairLayout)
          targetPairCode value (needed.flatMap (fun sample => [65535, sample]) ++ [88]) with
      | none => throwError "pair final target failed"
      | some (answer, framed, capacity, register, tape, scratch, events, remaining, elapsed) =>
        unless answer == (23, pairEntries) && framed == #[77] && capacity == 4 && register == 91 &&
            tape == 9 && scratch && events == trace && remaining == [88] && elapsed ≤ targetPairTime do
          throwError "pair final target changed scalar extraction, ignored beta, shared cache, frame or cost"
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``WeightedTarget.refines, ``WeightedTarget.cache_growth, ``WeightedTarget.denote_source,
      ``WeightedTarget.denote_encoded, ``WeightedTarget.denote_equiv, ``WeightedTarget.observe_equiv,
      ``WeightedTarget.time_bound, ``WeightedTarget.code_bound, ``WeightedTarget.names,
      ``WeightedTarget.buffers, ``WeightedTarget.descriptionFits, ``WeightedTarget.resources,
      ``targetBound, ``targetPairBound, ``targetFits, ``targetOracle, ``targetMemory] do
    for dependency in (← collectAxioms name) do
      unless dependency ∈ allowed do throwError "unexpected axiom {dependency} in {name}"

-- Signing and target evaluation now execute consecutively in the same program.
private def tailCode := WeightedSignatureTail.code (base := base) (key := .atom false) (val := .atom true)
  extractionLayout ⟨0, trivial⟩ ⟨0, trivial⟩ ⟨99, trivial⟩ oopsGenerator
  primitives comparison comparison_correct goodUpdate goodBuffers (by decide)
  goodExtract goodExtractBuffers (by decide) uniformPort uniformDraw
private def tailProximityCode := WeightedSignatureTail.code (base := base) (key := .atom false) (val := .atom true)
  extractionProximityLayout ⟨0, trivial⟩ ⟨0, trivial⟩ ⟨99, trivial⟩ proximityGenerator
  primitives comparison comparison_correct goodUpdate goodBuffers (by decide)
  goodExtract goodExtractBuffers (by decide) uniformPort uniformDraw
private def tailPairCode := WeightedSignatureTail.code (base := base) (key := .atom false)
  (val := .pair (.atom true) (.atom true)) extractionPairLayout ⟨0, trivial⟩ ⟨(0, 0), trivial, trivial⟩
  ⟨(99, 98), trivial, trivial⟩ oopsGenerator primitives comparison comparison_correct badUpdate badBuffers (by decide)
  badExtract badExtractBuffers (by decide) uniformPort uniformPairDraw
private def tailInput (signing : extractionLayout.input.Value) (forged : Word 16 × Word 16) (numerator : Word 16) :
    WeightedSignatureTail.Input extractionLayout :=
  (signing, ⟨(forged, numerator), ⟨trivial, trivial⟩, trivial⟩)
private def tailTime := WeightedSignatureTail.timeBudget (base := base) (key := .atom false) (val := .atom true)
  extractionLayout (OOPSTerms.timeBudget oops 6) 26 (BLSAccumulate.goodTime accumulation.arithmetic 6 6)
    (BLSExtractArithmetic.goodTime accumulation.arithmetic 6 6)
private def tailWords := WeightedSignatureTail.codeBudget (base := base) (key := .atom false) (val := .atom true)
  extractionLayout (OOPSTerms.codeBudget oops 27) 125 (BLSAccumulate.goodCode accumulation.arithmetic 27 27)
    (BLSExtractArithmetic.goodCode accumulation.arithmetic 27 27)
private def tailPairTime := WeightedSignatureTail.timeBudget (base := base) (key := .atom false)
  (val := .pair (.atom true) (.atom true)) extractionPairLayout
    (OOPSTerms.timeBudget oops 6) (PairSampling.timeBudget scalar scalar 26 26)
    (BLSAccumulate.badTime accumulation.arithmetic 6 6) (BLSExtractArithmetic.badTime accumulation.arithmetic 6 118 6)
private theorem tailBound : Interactive.TimeBoundOn (WeightedSignatureTail.ready extractionLayout)
    uniformPort .unit (WeightedSignatureTail.input extractionLayout) tailCode tailTime :=
  WeightedSignatureTail.time_bound (base := base) (key := .atom false) (val := .atom true)
    extractionLayout ⟨0, trivial⟩ ⟨0, trivial⟩ ⟨99, trivial⟩ oopsGenerator
    primitives comparison comparison_correct goodUpdate goodBuffers (by decide)
    goodExtract goodExtractBuffers (by decide) uniformPort uniformCorrect
    oopsBound (UniformSampling.time_bound (w := 16) 65535 (by decide) (by decide) 65535) goodBound goodExtractBound
private theorem tailPairBound : Interactive.TimeBoundOn (WeightedSignatureTail.ready extractionPairLayout)
    uniformPort .unit (WeightedSignatureTail.input extractionPairLayout) tailPairCode tailPairTime :=
  WeightedSignatureTail.time_bound (base := base) (key := .atom false) (val := .pair (.atom true) (.atom true))
    extractionPairLayout ⟨0, trivial⟩ ⟨(0, 0), trivial, trivial⟩ ⟨(99, 98), trivial, trivial⟩ oopsGenerator
    primitives comparison comparison_correct badUpdate badBuffers (by decide)
    badExtract badExtractBuffers (by decide) uniformPort uniformPairCorrect oopsBound
    (PairSampling.time_bound uniformCorrect uniformCorrect
      (UniformSampling.time_bound (w := 16) 65535 (by decide) (by decide) 65535)
      (UniformSampling.time_bound (w := 16) 65535 (by decide) (by decide) 65535))
    (BLSAccumulate.bad_bounded accumulation.arithmetic mul add mulBound addBound mulNames.buffers (by decide) addNames.buffers)
    badExtractBound
private theorem tailFits : (tailCode.lower uniformPort).DescriptionFits :=
  WeightedSignatureTail.descriptionFits (base := base) (key := .atom false) (val := .atom true)
    extractionLayout ⟨0, trivial⟩ ⟨0, trivial⟩ ⟨99, trivial⟩ oopsGenerator
    primitives comparison comparison_correct goodUpdate goodBuffers (by decide)
    goodExtract goodExtractBuffers (by decide) uniformPort uniformDraw
    (OOPSTerms.buffers oops trivial mul mulNames.buffers (by decide)) (by decide)
    (UniformSampling.descriptionFits (w := 16) 65535 (by decide) (by decide) 65535)
    (UniformSampling.names (w := 16) 65535 (by decide) (by decide) 65535) (by decide) (by decide)
private theorem tailBufferBound : (tailCode.lower uniformPort).memBound ≤ 14 :=
  WeightedSignatureTail.buffers (base := base) (key := .atom false) (val := .atom true)
    extractionLayout ⟨0, trivial⟩ ⟨0, trivial⟩ ⟨99, trivial⟩ oopsGenerator
    primitives comparison comparison_correct goodUpdate goodBuffers (by decide)
    goodExtract goodExtractBuffers (by decide) uniformPort uniformDraw
    (OOPSTerms.buffers oops trivial mul mulNames.buffers (by decide))
    (UniformSampling.names (w := 16) 65535 (by decide) (by decide) 65535).buffers
private theorem tailOracle (tape : RandomTape 16) (value : WeightedSignatureTail.Input extractionLayout)
    (admitted : WeightedSignatureTail.ready extractionLayout value) (before : State 16)
    (holds : (WeightedSignatureTail.input extractionLayout).Holds value before) :
    (fun result => (fun answer => (answer.val.1, answer.val.2.map (Prod.map Prod.swap id))) <$>
        Interactive.observe (WeightedSignatureTail.output extractionLayout).representation result) <$>
      tailCode.execute uniformPort .unit tape before =
      some <$> (do
        let signatures ← (simulateQ (BLS.LazyAGM.Reduction.privateListOracle (M := Word 16 × Fin 4) (R := Word 16))
          (Model.LazyAGM.evalTerms (Model.LazyAGM.WeightedReduction.signedTerms (OOPS.LazyAGM.terms 3)
            value.1.val.1.2 value.1.val.1.1.reverse))).run (value.1.val.2.map (Prod.map Prod.swap id))
        (fun target => (value.2.val.2 / (target.1 - signatures.1), target.2)) <$>
          (simulateQ (BLS.LazyAGM.Reduction.privateListOracle (M := Word 16 × Fin 4) (R := Word 16))
            (Model.LazyAGM.evalTerms (OOPS.LazyAGM.terms 3 value.2.val.1))).run signatures.2) :=
  WeightedSignatureTail.observe_equiv (base := base) (key := .atom false) (val := .atom true)
    extractionLayout ⟨0, trivial⟩ ⟨0, trivial⟩ ⟨99, trivial⟩ oopsGenerator
    primitives comparison comparison_correct goodUpdate goodBuffers (by decide)
    goodExtract goodExtractBuffers (by decide) (fun _ => rfl) rfl rfl uniformSource uniformLaw
    (Equiv.prodComm (Word 16) (Fin 4)) (OOPS.LazyAGM.terms 3) (OOPSTerms.source 3)
    uniformPort uniformDraw uniformCorrect tape value admitted before holds
private theorem tailMemory (tape : RandomTape 16) (value : WeightedSignatureTail.Input extractionLayout)
    (admitted : WeightedSignatureTail.ready extractionLayout value) (before : State 16)
    (holds : (WeightedSignatureTail.input extractionLayout).Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result 16) (reached : some finished ∈ support (tailCode.execute uniformPort .unit tape before)) :
    finished.time ≤ tailTime ∧
      ∃ execution : WordIO.Exec .unit tape (tailCode.lower uniformPort) before finished.state
          finished.trace finished.time finished.net finished.peak,
        ∀ between, execution.Visits between →
          ((tailCode.lower uniformPort).staticWords registers buffers : Int) +
            between.liveMem (max buffers (tailCode.lower uniformPort).memBound) ≤
              5 * tailWords + 20 + registers + 3 * buffers + before.liveMem buffers + tailTime := by
  obtain ⟨elapsed, _, _, _, execution, memory⟩ :=
    WeightedSignatureTail.resources (base := base) (key := .atom false) (val := .atom true)
      extractionLayout ⟨0, trivial⟩ ⟨0, trivial⟩ ⟨99, trivial⟩ oopsGenerator
      primitives comparison comparison_correct goodUpdate goodBuffers (by decide)
      goodExtract goodExtractBuffers (by decide) uniformPort uniformDraw uniformCorrect oopsBound
      (UniformSampling.time_bound (w := 16) 65535 (by decide) (by decide) 65535)
      (UniformSampling.code_words (w := 16) 65535 (by decide) (by decide) 65535)
      goodBound goodExtractBound oopsNames
      (UniformSampling.names (w := 16) 65535 (by decide) (by decide) 65535) goodNames goodExtractNames
      tape value admitted before holds registers buffers initialRegisters initialBuffers finished reached
  exact ⟨elapsed, execution, fun between visited => (memory between visited).2.2.2⟩

open Lean in
run_cmd do
  let samples : List (Word 16) := [2, 5, 7, 11]
  let moreSamples : List (Word 16) := [3, 7, 11, 13]
  let moreCache : List (Key × Word 16) := [((3, 43), 13), ((2, 43), 11), ((1, 43), 7), ((0, 43), 3)]
  let signed := extractionInput [(message.val, 13)] [5] [] (by decide) (by decide) (by decide)
  let missing := extractionInput [(message.val, 13)] [] [] (by decide) (by decide) (by decide)
  let explicitZero := extractionInput [(message.val, 13)] [0] [] (by decide) (by decide) (by decide)
  let surplus := extractionInput [(message.val, 13)] [5, 99] [] (by decide) (by decide) (by decide)
  let empty := extractionInput [] [5] [] (by decide) (by decide) (by decide)
  let cached := extractionInput [] [5] entries (by decide) (by decide) (by decide)
  let cases : List (WeightedSignatureTail.Input extractionLayout × List (Word 16) × Word 16 × List (Key × Word 16)) :=
    [(tailInput signed message.val 64028, samples, 1, entries),
     (tailInput signed (2, 43) 63816, samples ++ moreSamples, 1, moreCache ++ entries),
     (tailInput missing message.val 754, samples, 2, entries),
     (tailInput explicitZero message.val 754, samples, 2, entries),
     (tailInput surplus message.val 64028, samples, 1, entries),
     (tailInput empty message.val 754, samples, 2, entries),
     (tailInput cached message.val 754, [], 2, entries)]
  for (value, draws, expected, cache) in cases do
    unless decide (WeightedSignatureTail.ready extractionLayout value) do
      throwError "signature tail admission used padded transcript capacity"
    match executeUniform (WeightedSignatureTail.input extractionLayout) (WeightedSignatureTail.output extractionLayout)
        tailCode value (draws.flatMap (fun sample => [65535, sample]) ++ [88]) with
    | none => throwError "composed signature/target execution failed"
    | some (answer, framed, capacity, register, tape, scratch, events, remaining, elapsed) =>
      let trace := draws.flatMap (fun sample => [WordIO.Event.output 65535, .invoke, .input 65535, .input sample])
      unless answer == (expected, cache) && framed == #[77] && capacity == 4 && register == 91 &&
          tape == 9 && scratch && events == trace && remaining == [88] && elapsed ≤ tailTime do
        throwError "signature tail lost shared cache, coefficient/default behavior, forgery context, frame or budget"
  let noRoom := tailInput (extractionInput [(message.val, 13)] [5] entries
    (by decide) (by decide) (by decide)) message.val 64028
  unless !(decide (WeightedSignatureTail.ready extractionLayout noRoom)) do
    throwError "signature tail did not reserve target terms"
  let psigning : extractionProximityLayout.input.Value :=
    ⟨(([( (vector 3 9 27).val, 13)], [5]), []),
      ⟨⟨by decide, fun _ _ => ⟨⟨(fun _ => trivial), trivial⟩, trivial⟩⟩, by decide, fun _ _ => trivial⟩,
      by decide, by simp⟩
  let pvalue : WeightedSignatureTail.Input extractionProximityLayout :=
    (psigning, ⟨(((vector 2 4 8).val.1, 43), 63816), ⟨(fun _ => trivial), trivial⟩, trivial⟩)
  let allSamples := samples ++ moreSamples
  match executeUniform (WeightedSignatureTail.input extractionProximityLayout) (WeightedSignatureTail.output extractionProximityLayout)
      tailProximityCode pvalue (allSamples.flatMap (fun sample => [65535, sample]) ++ [88]) with
  | none => throwError "composed Proximity signature/target execution failed"
  | some (answer, framed, capacity, register, tape, scratch, events, remaining, _) =>
    let trace := allSamples.flatMap (fun sample => [WordIO.Event.output 65535, .invoke, .input 65535, .input sample])
    unless answer == (1, moreCache ++ entries) && framed == #[77] && capacity == 4 && register == 91 &&
        tape == 9 && scratch && events == trace && remaining == [88] do
      throwError "Proximity signature tail changed vector evaluation, cache order or retained context"
  let pairSamples : List (Word 16) := [2, 3, 5, 7, 11, 13, 17, 19]
  let pairCache : List (Key × (Word 16 × Word 16)) :=
    [((3, 42), (17, 19)), ((2, 42), (11, 13)), ((1, 42), (5, 7)), ((0, 42), (2, 3))]
  let pairSigning : extractionPairLayout.input.Value :=
    ⟨(([(message.val, 13)], [1]), []),
      ⟨⟨by decide, fun _ _ => ⟨⟨trivial, trivial⟩, trivial⟩⟩, by decide, fun _ _ => trivial⟩, by decide, by simp⟩
  let pairCases : List ((Word 16 × Word 16) × List (Word 16) × Word 16 × List (Key × (Word 16 × Word 16))) :=
    [(message.val, pairSamples, 0, pairCache),
     ((0, 43), pairSamples ++ [577, 700, 5, 7, 11, 13, 17, 19], 32745,
       [((3, 43), (17, 19)), ((2, 43), (11, 13)), ((1, 43), (5, 7)), ((0, 43), (577, 700))] ++ pairCache)]
  for (forged, draws, expected, cache) in pairCases do
    let value : WeightedSignatureTail.Input extractionPairLayout :=
      (pairSigning, ⟨(forged, 999), ⟨trivial, trivial⟩, trivial⟩)
    match executeUniform (WeightedSignatureTail.input extractionPairLayout) (WeightedSignatureTail.output extractionPairLayout)
        tailPairCode value (draws.flatMap (fun sample => [65535, sample]) ++ [88]) with
    | none => throwError "composed pair signature/target execution failed"
    | some (answer, framed, capacity, register, tape, scratch, events, remaining, elapsed) =>
      let trace := draws.flatMap (fun sample => [WordIO.Event.output 65535, .invoke, .input 65535, .input sample])
      unless answer == (expected, cache) && framed == #[77] && capacity == 4 && register == 91 &&
          tape == 9 && scratch && events == trace && remaining == [88] && elapsed ≤ tailPairTime do
        throwError "pair signature tail changed cache sharing, scalar result, ignored beta, frame or time"
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``WeightedSignatureTail.refines, ``WeightedSignatureTail.preserves, ``WeightedSignatureTail.denote_source,
      ``WeightedSignatureTail.denote_encoded, ``WeightedSignatureTail.denote_equiv, ``WeightedSignatureTail.observe_equiv,
      ``WeightedExtraction.buffers, ``WeightedExtraction.savedNameFits,
      ``WeightedSignatureTail.time_bound, ``WeightedSignatureTail.code_bound, ``WeightedSignatureTail.names,
      ``WeightedSignatureTail.buffers, ``WeightedSignatureTail.descriptionFits, ``WeightedSignatureTail.resources,
      ``tailBound, ``tailPairBound, ``tailFits, ``tailBufferBound, ``tailOracle, ``tailMemory] do
    for dependency in (← collectAxioms name) do
      unless dependency ∈ allowed do throwError "unexpected axiom {dependency} in {name}"

-- Complete extraction has independent hash/sign keys and coefficient capacities.
private def extractorAccumulation : BLSPrivateAccumulate.Layouts 16 Key (Word 16) where
  cache := { accumulation.cache with capacityPred := 9, countFits := by decide, storageFits := by decide }
  pairStorageFits := by decide
  scalarStorageFits := by decide
  goodStorageFits := by decide
  badStorageFits := by decide
private def extractorSigning : WeightedExtraction.Layouts 16 Key (Word 16 × Word 16) (Word 16) (Word 16) (Word 16) :=
  ⟨⟨⟨extractorAccumulation.good, oops.input, by decide⟩, scalar, by decide⟩,
    3, 4, 4, by decide, by decide, by decide, by decide, by decide⟩
private def extractorLayout : WeightedExtractor.Layouts 16 Key (Word 16 × Word 16) (Word 16) (Word 16) (Word 16) :=
  ⟨extractorSigning, 2, 3, by decide, by decide, by decide⟩
private def extractorProximitySigning :
    WeightedExtraction.Layouts 16 Key ((Fin 3 → Word 16) × Word 16) (Word 16) (Word 16) (Word 16) :=
  ⟨⟨⟨extractorAccumulation.good, proximity.input, by decide⟩, scalar, by decide⟩,
    3, 4, 4, by decide, by decide, by decide, by decide, by decide⟩
private def extractorProximityLayout :
    WeightedExtractor.Layouts 16 Key ((Fin 3 → Word 16) × Word 16) (Word 16) (Word 16) (Word 16) :=
  ⟨extractorProximitySigning, 2, 3, by decide, by decide, by decide⟩
private def extractorPairSigning :
    WeightedExtraction.Layouts 16 Key (Word 16 × Word 16) (Word 16) (Word 16) (Word 16 × Word 16) :=
  ⟨⟨⟨extractorAccumulation.bad, oops.input, by decide⟩, scalar, by decide⟩,
    3, 4, 4, by decide, by decide, by decide, by decide, by decide⟩
private def extractorPairLayout :
    WeightedExtractor.Layouts 16 Key (Word 16 × Word 16) (Word 16) (Word 16) (Word 16 × Word 16) :=
  ⟨extractorPairSigning, 2, 3, by decide, by decide, by decide⟩
private def extractorCode := WeightedExtractor.code (base := base) (key := .atom false) (val := .atom true)
  extractorLayout ⟨0, trivial⟩ ⟨0, trivial⟩ ⟨99, trivial⟩ oopsGenerator primitives comparison comparison_correct
  goodUpdate goodBuffers (by decide) goodExtract goodExtractBuffers (by decide) add addNames.buffers (by decide) uniformPort uniformDraw
private def extractorProximityCode := WeightedExtractor.code (base := base) (key := .atom false) (val := .atom true)
  extractorProximityLayout ⟨0, trivial⟩ ⟨0, trivial⟩ ⟨99, trivial⟩ proximityGenerator primitives comparison comparison_correct
  goodUpdate goodBuffers (by decide) goodExtract goodExtractBuffers (by decide) add addNames.buffers (by decide) uniformPort uniformDraw
private def extractorPairCode := WeightedExtractor.badCode (base := base) (key := .atom false) (val := .pair (.atom true) (.atom true))
  extractorPairLayout ⟨0, trivial⟩ ⟨(0, 0), trivial, trivial⟩ ⟨(99, 98), trivial, trivial⟩ oopsGenerator
  primitives comparison comparison_correct badUpdate badBuffers (by decide)
  badExtract badExtractBuffers (by decide) uniformPort uniformPairDraw
private def extractorInput (forged : Word 16 × Word 16) (beta : Word 16)
    (gamma xi : List (Word 16)) (hashes : List (Key × Word 16))
    (signs : List ((Word 16 × Word 16) × Word 16)) (cache : List (Key × Word 16))
    (gammaBound : gamma.length ≤ 3) (xiBound : xi.length ≤ 4) (hashBound : hashes.length ≤ 2)
    (signBound : signs.length ≤ 3) (cacheBound : cache.length ≤ 10) : extractorLayout.input.Value :=
  ⟨((forged, beta, gamma, xi), (cache, hashes, signs)),
    ⟨⟨trivial, trivial⟩, trivial, ⟨gammaBound, fun _ _ => trivial⟩, xiBound, fun _ _ => trivial⟩,
    ⟨cacheBound, fun _ _ => ⟨⟨trivial, trivial⟩, trivial⟩⟩,
    ⟨hashBound, fun _ _ => ⟨⟨trivial, trivial⟩, trivial⟩⟩,
    signBound, fun _ _ => ⟨⟨trivial, trivial⟩, trivial⟩⟩
private def extractorTime := WeightedExtractor.timeBudget (base := base) (key := .atom false) (val := .atom true)
  extractorLayout (OOPSTerms.timeBudget oops 6) 26 (BLSAccumulate.goodTime accumulation.arithmetic 6 6)
    (BLSExtractArithmetic.goodTime accumulation.arithmetic 6 6) 6
private def extractorWords := WeightedExtractor.codeBudget (base := base) (key := .atom false) (val := .atom true)
  extractorLayout (OOPSTerms.codeBudget oops 27) 125 (BLSAccumulate.goodCode accumulation.arithmetic 27 27)
    (BLSExtractArithmetic.goodCode accumulation.arithmetic 27 27) 27
private def extractorPairTime := WeightedExtractor.badTimeBudget (base := base) (key := .atom false)
  (val := .pair (.atom true) (.atom true)) extractorPairLayout (OOPSTerms.timeBudget oops 6)
    (PairSampling.timeBudget scalar scalar 26 26) (BLSAccumulate.badTime accumulation.arithmetic 6 6)
    (BLSExtractArithmetic.badTime accumulation.arithmetic 6 118 6)
private theorem extractorBound : Interactive.TimeBoundOn extractorLayout.ready uniformPort .unit
    extractorLayout.input.representation extractorCode extractorTime :=
  WeightedExtractor.time_bound (base := base) (key := .atom false) (val := .atom true)
    extractorLayout ⟨0, trivial⟩ ⟨0, trivial⟩ ⟨99, trivial⟩ oopsGenerator primitives comparison comparison_correct
    goodUpdate goodBuffers (by decide) goodExtract goodExtractBuffers (by decide) add addNames.buffers (by decide)
    uniformPort uniformCorrect oopsBound (UniformSampling.time_bound (w := 16) 65535 (by decide) (by decide) 65535)
    goodBound goodExtractBound addBound
private theorem extractorFits : (extractorCode.lower uniformPort).DescriptionFits :=
  WeightedExtractor.descriptionFits (base := base) (key := .atom false) (val := .atom true)
    extractorLayout ⟨0, trivial⟩ ⟨0, trivial⟩ ⟨99, trivial⟩ oopsGenerator primitives comparison comparison_correct
    goodUpdate goodBuffers (by decide) goodExtract goodExtractBuffers (by decide) add addNames.buffers (by decide)
    uniformPort uniformDraw (OOPSTerms.buffers oops trivial mul mulNames.buffers (by decide)) (by decide)
    (UniformSampling.descriptionFits (w := 16) 65535 (by decide) (by decide) 65535)
    (UniformSampling.names (w := 16) 65535 (by decide) (by decide) 65535) (by decide) (by decide)
private theorem extractorOracle (tape : RandomTape 16) (value : extractorLayout.input.Value)
    (admitted : extractorLayout.ready value) (before : State 16) (holds : extractorLayout.input.representation.Holds value before) :
    (fun result => (fun answer => (answer.val.1, answer.val.2.map (Prod.map Prod.swap id))) <$>
        Interactive.observe (WeightedSignatureTail.output extractorSigning).representation result) <$>
      extractorCode.execute uniformPort .unit tape before =
      some <$> WeightedExtractor.sourceProgram extractorLayout (OOPS.LazyAGM.terms 3)
        (fun value => value.1 + value.2) (fun value => value.1 / (value.2.1 - value.2.2)) value
        (value.val.2.2.1.map (Prod.map Prod.swap id)) (value.val.2.1.map (Prod.map Prod.swap id)) :=
  WeightedExtractor.observe_equiv (base := base) (key := .atom false) (val := .atom true)
    extractorLayout ⟨0, trivial⟩ ⟨0, trivial⟩ ⟨99, trivial⟩ oopsGenerator primitives comparison comparison_correct
    goodUpdate goodBuffers (by decide) goodExtract goodExtractBuffers (by decide) add
    (fun _ => rfl) rfl rfl uniformSource uniformLaw (Equiv.prodComm (Word 16) (Fin 4))
    (OOPS.LazyAGM.terms 3) (OOPSTerms.source 3) addNames.buffers (by decide)
    uniformPort uniformDraw uniformCorrect tape value admitted before holds
private theorem extractorMemory (tape : RandomTape 16) (value : extractorLayout.input.Value)
    (admitted : extractorLayout.ready value) (before : State 16) (holds : extractorLayout.input.representation.Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result 16) (reached : some finished ∈ support (extractorCode.execute uniformPort .unit tape before)) :
    finished.time ≤ extractorTime ∧
      ∃ execution : WordIO.Exec .unit tape (extractorCode.lower uniformPort) before finished.state
          finished.trace finished.time finished.net finished.peak,
        ∀ between, execution.Visits between →
          ((extractorCode.lower uniformPort).staticWords registers buffers : Int) +
            between.liveMem (max buffers (extractorCode.lower uniformPort).memBound) ≤
              5 * extractorWords + 80 + registers + 3 * buffers + before.liveMem buffers + extractorTime := by
  obtain ⟨elapsed, _, _, _, execution, memory⟩ :=
    WeightedExtractor.resources (base := base) (key := .atom false) (val := .atom true)
      extractorLayout ⟨0, trivial⟩ ⟨0, trivial⟩ ⟨99, trivial⟩ oopsGenerator primitives comparison comparison_correct
      goodUpdate goodBuffers (by decide) goodExtract goodExtractBuffers (by decide) add addNames.buffers (by decide)
      uniformPort uniformDraw uniformCorrect oopsBound
      (UniformSampling.time_bound (w := 16) 65535 (by decide) (by decide) 65535)
      (UniformSampling.code_words (w := 16) 65535 (by decide) (by decide) 65535) goodBound goodExtractBound
      oopsNames (UniformSampling.names (w := 16) 65535 (by decide) (by decide) 65535) goodNames goodExtractNames addBound addNames.accounted
      tape value admitted before holds registers buffers initialRegisters initialBuffers finished reached
  exact ⟨elapsed, execution, fun between visited => (memory between visited).2.2.2⟩

open Lean in
run_cmd do
  let hashes : List (Key × Word 16) := [((1, 42), 13), ((0, 42), 17)]
  let signs : List ((Word 16 × Word 16) × Word 16) := [(message.val, 23)]
  let samples : List (Word 16) := [2, 5, 7, 11]
  let more : List (Word 16) := [3, 7, 11, 13]
  let moreCache : List (Key × Word 16) := [((3, 43), 13), ((2, 43), 11), ((1, 43), 7), ((0, 43), 3)]
  let reused := extractorInput message.val 64002 [3, 4] [5] hashes signs []
    (by decide) (by decide) (by decide) (by decide) (by decide)
  let runtimeZero := extractorInput message.val 65510 [3, 4] [5] hashes signs []
    (by decide) (by decide) (by decide) (by decide) (by decide)
  let distinct := extractorInput (2, 43) 63790 [3, 4] [5] hashes signs []
    (by decide) (by decide) (by decide) (by decide) (by decide)
  let padded := extractorInput message.val 64002 [3, 4, 99] [5, 98] hashes signs []
    (by decide) (by decide) (by decide) (by decide) (by decide)
  let missingSign := extractorInput message.val 728 [3, 4] [] hashes signs []
    (by decide) (by decide) (by decide) (by decide) (by decide)
  let cached := extractorInput message.val 728 [3, 4] [] hashes [] entries
    (by decide) (by decide) (by decide) (by decide) (by decide)
  let empty := extractorInput message.val 754 [] [] [] [] []
    (by decide) (by decide) (by decide) (by decide) (by decide)
  let cases : List (extractorLayout.input.Value × List (Word 16) × Word 16 × List (Key × Word 16)) :=
    [(reused, samples, 1, entries), (runtimeZero, samples, 0, entries),
     (distinct, samples ++ more, 1, moreCache ++ entries), (padded, samples, 1, entries),
     (missingSign, samples, 2, entries), (cached, [], 2, entries), (empty, samples, 2, entries)]
  for (value, draws, expected, cache) in cases do
    unless decide (extractorLayout.ready value) do throwError "full extractor rejected occupied transcript bounds"
    match executeUniform extractorLayout.input.representation (WeightedSignatureTail.output extractorSigning)
        extractorCode value (draws.flatMap (fun sample => [65535, sample]) ++ [88]) with
    | none => throwError "complete weighted extractor failed"
    | some (answer, framed, capacity, register, tape, scratch, events, remaining, elapsed) =>
      let trace := draws.flatMap (fun sample => [WordIO.Event.output 65535, .invoke, .input 65535, .input sample])
      unless answer == (expected, cache) && framed == #[77] && capacity == 4 && register == 91 && tape == 9 &&
          scratch && events == trace && remaining == [88] && elapsed ≤ extractorTime do
        throwError "full extractor changed runtime numerator, chronological coefficients, cache sharing, frame or time: expected={expected.toNat}, actual={answer.1.toNat}"
  let unrelatedHashes : List (Key × Word 16) := [((0, 78), 13), ((0, 77), 17)]
  for gamma in ([⟨[], by decide⟩, ⟨[0, 0], by decide⟩] : List {gamma : List (Word 16) // gamma.length ≤ 3}) do
    let value := extractorInput message.val 64028 gamma.val [5] unrelatedHashes signs []
      gamma.property (by decide) (by decide) (by decide) (by decide)
    let draws := [17, 19] ++ samples
    match executeUniform extractorLayout.input.representation (WeightedSignatureTail.output extractorSigning)
        extractorCode value (draws.flatMap (fun sample => [65535, sample]) ++ [88]) with
    | none => throwError "zero/default hash coefficients failed"
    | some (answer, _, _, _, _, scratch, events, remaining, elapsed) =>
      let trace := draws.flatMap (fun sample => [WordIO.Event.output 65535, .invoke, .input 65535, .input sample])
      unless answer == (1, entries ++ [((0, 78), 19), ((0, 77), 17)]) && scratch && events == trace &&
          remaining == [88] && elapsed ≤ extractorTime do
        throwError "zero/default hash coefficients skipped source reads or lost unrelated entries"
  let noRoom := extractorInput message.val 64002 [3, 4] [5] hashes signs (List.replicate 1 ((0, 99), 123))
    (by decide) (by decide) (by decide) (by decide) (by decide)
  unless !(decide (extractorLayout.ready noRoom)) do throwError "full extraction failed to reserve hash/sign/target room"
  let pvalue : extractorProximityLayout.input.Value :=
    ⟨((((vector 2 4 8).val.1, 43), 63790, [3, 4], [5]), ([], hashes, [((vector 3 9 27).val, 23)])),
      ⟨⟨(fun _ => trivial), trivial⟩, trivial, ⟨by decide, fun _ _ => trivial⟩, by decide, fun _ _ => trivial⟩,
      ⟨by decide, by simp⟩, ⟨by decide, fun _ _ => ⟨⟨trivial, trivial⟩, trivial⟩⟩,
      by decide, fun _ _ => ⟨⟨(fun _ => trivial), trivial⟩, trivial⟩⟩
  let draws := samples ++ more
  match executeUniform extractorProximityLayout.input.representation (WeightedSignatureTail.output extractorProximitySigning)
      extractorProximityCode pvalue (draws.flatMap (fun sample => [65535, sample]) ++ [88]) with
  | none => throwError "complete Proximity extractor failed"
  | some (answer, framed, capacity, register, tape, scratch, events, remaining, _) =>
    let trace := draws.flatMap (fun sample => [WordIO.Event.output 65535, .invoke, .input 65535, .input sample])
    unless answer == (1, moreCache ++ entries) && framed == #[77] && capacity == 4 && register == 91 && tape == 9 &&
        scratch && events == trace && remaining == [88] do
      throwError "complete Proximity extractor changed vector/hash composition"
  let pairSamples : List (Word 16) := [2, 3, 5, 7, 11, 13, 17, 19]
  let pairCache : List (Key × (Word 16 × Word 16)) :=
    [((3, 42), (17, 19)), ((2, 42), (11, 13)), ((1, 42), (5, 7)), ((0, 42), (2, 3))]
  let pairCases : List ((Word 16 × Word 16) × List (Word 16) × Word 16 × List (Key × (Word 16 × Word 16))) :=
    [(message.val, pairSamples, 0, pairCache),
     ((0, 43), pairSamples ++ [577, 700, 5, 7, 11, 13, 17, 19], 32745,
       [((3, 43), (17, 19)), ((2, 43), (11, 13)), ((1, 43), (5, 7)), ((0, 43), (577, 700))] ++ pairCache)]
  for (forged, draws, expected, cache) in pairCases do
    for beta in ([0, 999] : List (Word 16)) do
      let value : extractorPairLayout.input.Value :=
        ⟨((forged, beta, [111, 222, 333], [1]), ([], unrelatedHashes, signs)),
          ⟨⟨trivial, trivial⟩, trivial,
            ⟨by change (3 : Nat) ≤ 3; decide, fun _ _ => trivial⟩,
            (by change (1 : Nat) ≤ 4; decide), fun _ _ => trivial⟩,
          ⟨by change (0 : Nat) ≤ 10; decide, by simp⟩,
          ⟨by change (2 : Nat) ≤ 2; decide, fun _ _ => ⟨⟨trivial, trivial⟩, trivial⟩⟩,
          (by change (1 : Nat) ≤ 3; decide), fun _ _ => ⟨⟨trivial, trivial⟩, trivial⟩⟩
      unless decide (extractorPairLayout.badReady value) do throwError "bad extractor rejected its signing/target reservation"
      match executeUniform extractorPairLayout.input.representation (WeightedSignatureTail.output extractorPairSigning)
          extractorPairCode value (draws.flatMap (fun sample => [65535, sample]) ++ [88]) with
      | none => throwError "complete pair extractor failed"
      | some (answer, framed, capacity, register, tape, scratch, events, remaining, elapsed) =>
        let trace := draws.flatMap (fun sample => [WordIO.Event.output 65535, .invoke, .input 65535, .input sample])
        unless answer == (expected, cache) && framed == #[77] && capacity == 4 && register == 91 && tape == 9 &&
            scratch && events == trace && remaining == [88] && elapsed ≤ extractorPairTime do
          throwError "bad extractor evaluated ignored hash rows, used beta or changed shared cache/framing"
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``TokenEvaluation.evalTerms_source, ``WeightedExtractor.refines, ``WeightedExtractor.bad_refines,
      ``WeightedExtractor.hashPreserves, ``WeightedExtractor.denote_source, ``WeightedExtractor.bad_denote_source,
      ``WeightedExtractor.denote_encoded, ``WeightedExtractor.denote_equiv, ``WeightedExtractor.observe_equiv,
      ``WeightedExtractor.transition_time, ``WeightedExtractor.transition_words, ``WeightedExtractor.transition_buffers,
      ``WeightedExtractor.time_bound, ``WeightedExtractor.code_bound, ``WeightedExtractor.bad_time_bound,
      ``WeightedExtractor.bad_code_bound, ``WeightedExtractor.names, ``WeightedExtractor.bad_names,
      ``WeightedExtractor.buffers, ``WeightedExtractor.descriptionFits, ``WeightedExtractor.bad_descriptionFits,
      ``WeightedExtractor.resources, ``WeightedExtractor.bad_resources,
      ``extractorBound, ``extractorFits, ``extractorOracle, ``extractorMemory] do
    for dependency in (← collectAxioms name) do
      unless dependency ∈ allowed do throwError "unexpected axiom {dependency} in {name}"

end SignaturesTest.CaliperGeneratedWeighted
