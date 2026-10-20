import Signatures.Runtime.Caliper.GeneratedWeightedBounds
import Signatures.Runtime.Caliper.OOPSTermsBounds
import Signatures.Runtime.Caliper.BLSRows
import Signatures.Runtime.Caliper.GeneratedWeightedOracle
import Signatures.Runtime.Caliper.UniformSampling
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

end SignaturesTest.CaliperGeneratedWeighted
