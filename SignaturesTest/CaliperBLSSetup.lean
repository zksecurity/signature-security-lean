import Signatures.Runtime.Caliper.BLSSetupResources
import Signatures.Runtime.Caliper.UniformQuery
import Lean

open Caliper OracleComp OracleSpec Signatures.Runtime Signatures.Runtime.CaliperBackend BoundedSource

namespace SignaturesTest.CaliperBLSSetup

-- Finite machine layouts over an infinite source message type. The executable
-- scale routine uses word arithmetic; this fixture is not a curve library.
private def cache : CacheLayout 16 Nat (Fin 4) where
  key := Layout.counter 16 65536 (by decide) (by decide)
  value := Layout.all (Representation.fin 16 4 (by decide) (by decide))
  capacityPred := 1
  wordFits := by decide
  countFits := by decide
  storageFits := by decide
private def scheme : BLSReply.SchemeLayouts 16 Nat (Fin 4) (Word 16) where
  cache := cache
  point := Layout.all (wordRepresentation 16 (by decide))
  responseFits := by decide
  capacityPred := 1
  countFits := by decide
  goodFits := by decide
  pairFits := by decide
  badFits := by decide
private def layout : BLSSetup.Layouts 16 Nat (Fin 4) (Word 16) (Word 16) where
  scheme := scheme
  key := Layout.all (wordRepresentation 16 (by decide))
  storageFits := by decide
private instance : SMul (Fin 4) (Word 16) where
  smul scalar point := BitVec.ofNat 16 scalar.val * point
private def scale : Implementation .unit layout.scaleArgs layout.key (fun value => value.1 • value.2) where
  preserves _ _ := trivial
  program := ((WordBinary.realizer .unit .mul (by decide)).viewInput layout.scaleArgs.representation
    (fun value => (BitVec.ofNat 16 value.val.1.val, value.val.2)) (fun _ => rfl)).viewOutput layout.key.representation
      (fun value => ⟨value.val.1 • value.val.2, trivial⟩) (fun _ => rfl)
private theorem scale_bound : scale.BoundedBy 6 27 := ⟨fun _ => le_rfl, by decide⟩
private theorem scale_names : NamesBound scale.program.code 3 := by constructor <;> decide

private def port := UniformQuery.port (w := 16) 3 (by decide) (by decide)
private def drawRequest : Realizer .unit cache.lookup.unit.representation port.request (fun _ => (3 : Fin 4)) :=
  (Implementation.constant cache.lookup.unit (Layout.all port.request) ⟨(3 : Fin 4), trivial⟩ (by decide)).program.viewOutput
    port.request (fun _ => (3 : Fin 4)) (fun _ => rfl)
private def drawValue (value : UniformQuery.Reply 3) : cache.value.Value :=
  ⟨⟨value.2.val, by have := value.1.isLt; have := value.2.isLt; omega⟩, trivial⟩
private def drawReply : Realizer .unit port.reply cache.value.representation drawValue :=
  selectSliceRealizer .unit (by decide) _ _ _ 1 (by decide) (by decide) (fun _ => rfl)
private def draw : Interactive.Code 16 := .seq (.compute drawRequest.code) (.seq .query (.compute drawReply.code))
private def drawSource : ProbComp cache.value.Value := drawValue <$> UniformQuery.source 3 3
private theorem draw_correct : Interactive.Refines port .unit cache.lookup.unit.representation cache.value.representation
    (fun _ => drawSource) draw := by
  have composed := (Interactive.Refines.compute port .unit drawRequest).seq
    ((UniformQuery.refines 3 (by decide) (by decide)).seq (Interactive.Refines.compute port .unit drawReply))
  convert composed using 1
  · funext value
    rfl
  · rfl
private theorem draw_law : Subtype.val <$> drawSource = ($ᵗ (Fin 4) : ProbComp (Fin 4)) := by
  simp only [drawSource, UniformQuery.source, Functor.map_map]
  rfl
private theorem draw_time : Interactive.TimeBound port .unit cache.lookup.unit.representation draw 26 := by
  have first := Interactive.TimeBound.compute (port := port) (cost := .unit) drawRequest 8
    (fun value => (Implementation.constant_bounded cache.lookup.unit (Layout.all port.request) ⟨(3 : Fin 4), trivial⟩ (by decide)).time_le value)
  have last := Interactive.TimeBound.compute (port := port) (cost := .unit) drawReply 8
    (by intro value; change (selectSlice (w := 16) 1 1).staticTime .unit ≤ 8; decide)
  exact first.seq (Interactive.Refines.compute port .unit drawRequest)
    ((UniformQuery.time_bound 3 (by decide) (by decide)).seq (UniformQuery.refines 3 (by decide) (by decide)) last)
private theorem draw_words : (draw.lower port).descriptionWords ≤ 200 := by decide
private theorem draw_names : WordIO.NamesBound (draw.lower port) 3 := by constructor <;> decide
private theorem draw_fits : (draw.lower port).DescriptionFits :=
  .seq (by decide) (.compute drawRequest.description_fits)
    (.seq (by decide) (UniformQuery.descriptionFits 3 (by decide) (by decide)) (.compute drawReply.description_fits))

private def good := BLSSetup.goodCode layout
private def bad := BLSSetup.badCode layout port draw scale scale_names.buffers (by decide)
private def goodInput : layout.challenge.Value := ⟨((3, 5), (7, 11)), by trivial⟩
private def changedInput : layout.challenge.Value := ⟨((13, 17), (19, 23)), by trivial⟩

private theorem good_reserved (value : layout.challenge.Value) :
    BLSReply.Reserved scheme.good 2 (value.val.1, [], [], []) :=
  BLSSetup.good_reserved layout 2 (by decide) (by decide) value
private theorem bad_reserved (value : layout.sampled.Value) :
    BLSReply.Reserved scheme.bad 2 ((value.val.1, value.val.2.1), [], [], []) :=
  BLSSetup.bad_reserved layout 2 (by decide) (by decide) value
example : ¬ (3 ≤ scheme.cache.capacityPred + 1) := by decide

private theorem good_source (tape : RandomTape 16) (value : layout.challenge.Value) (before : State 16)
    (holds : layout.challenge.representation.Holds value before) :
    (fun result => Subtype.val <$> Interactive.observe layout.goodOutput.representation result) <$>
      good.execute port .unit tape before = pure (some (value.val.2.2, value.val.1, [], [], [])) :=
  BLSSetup.good_observe layout port tape value before holds
private theorem bad_source (tape : RandomTape 16) (value : layout.challenge.Value) (before : State 16)
    (holds : layout.challenge.representation.Holds value before) :
    (fun result => Subtype.val <$> Interactive.observe layout.badOutput.representation result) <$>
      bad.execute port .unit tape before =
      (fun scalar => some (scalar • value.val.2.1, (scalar, value.val.1), [], [], [])) <$> ($ᵗ (Fin 4) : ProbComp (Fin 4)) :=
  BLSSetup.bad_observe layout port draw drawSource draw_correct scale scale_names.buffers (by decide) draw_law tape value before holds

private theorem good_time : Interactive.TimeBound port .unit layout.challenge.representation good (200 * layout.width) :=
  BLSSetup.good_time layout port
private theorem good_words : (good.lower port).descriptionWords ≤ 700 * layout.width + 251 :=
  BLSSetup.good_words layout port
private theorem bad_time : Interactive.TimeBound port .unit layout.challenge.representation bad (BLSSetup.badTime layout 26 6) :=
  BLSSetup.bad_time layout port draw drawSource draw_correct draw_time scale scale_names.buffers (by decide) scale_bound
private theorem bad_words : (bad.lower port).descriptionWords ≤ BLSSetup.badWords layout 200 27 :=
  BLSSetup.bad_words layout port draw draw_words scale scale_names.buffers (by decide) scale_bound
private theorem bad_fits : (bad.lower port).DescriptionFits :=
  BLSSetup.bad_descriptionFits layout port draw scale scale_names.buffers (by decide) draw_fits draw_names (by decide)
private theorem bad_memory (tape : RandomTape 16) (value : layout.challenge.Value) (before : State 16)
    (holds : layout.challenge.representation.Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result 16) (reached : some finished ∈ support (bad.execute port .unit tape before)) :
    ∃ execution : WordIO.Exec .unit tape (bad.lower port) before finished.state finished.trace finished.time finished.net finished.peak,
      ∀ between, execution.Visits between →
        ((bad.lower port).staticWords registers buffers : Int) + between.liveMem (max buffers (bad.lower port).memBound) ≤
          5 * BLSSetup.badWords layout 200 27 + 12 + registers + 3 * buffers + before.liveMem buffers + BLSSetup.badTime layout 26 6 := by
  have certified := BLSSetup.bad_resources layout port draw drawSource draw_correct draw_time draw_words scale scale_names.buffers
    (by decide) scale_bound draw_names scale_names.accounted tape value before holds registers buffers initialRegisters initialBuffers finished reached
  obtain ⟨_, _, _, _, execution, bounded⟩ := certified
  refine ⟨execution, fun between visited => ?_⟩
  have memory := (bounded between visited).2.2.2
  simp only [Nat.max_self] at memory
  dsimp only [bad]
  omega

private def execute (code : Interactive.Code 16) (value : layout.challenge.Value) (replies : List (Word 16)) :=
  let initial := layout.challenge.representation.initial value
  let before := { initial with bufs := fun b => if b = 200 then #[91] else initial.bufs b
                               caps := fun b => if b = 200 then 4 else initial.caps b
                               regs := fun r => if r = 200 then 99 else initial.regs r
                               tapePos := 9 }
  (WordIO.run .unit RandomTape.zero 200000 (code.lower port) before replies).map
    (fun finished => (finished.state.bufs 0, finished.trace, finished.remaining,
      finished.state.bufs 200, finished.state.caps 200, finished.state.regs 200, finished.state.tapePos))

open Lean in
run_cmd do
  let goodEmpty : Array (Word 16) := Array.replicate 15 0
  let badEmpty : Array (Word 16) := Array.replicate 17 0
  unless execute good goodInput [55] == some (#[11, 3, 5] ++ goodEmpty, [], [55], #[91], 4, 99, 9) do
    throwError "good setup failed to copy the runtime key/challenge or initialize cache/transcripts"
  unless execute good changedInput [55] == some (#[23, 13, 17] ++ goodEmpty, [], [55], #[91], 4, 99, 9) do
    throwError "good setup embedded its challenge instead of copying runtime input"
  unless execute bad goodInput [3, 2, 55] == some (#[14, 2, 3, 5] ++ badEmpty,
      [.output 3, .invoke, .input 3, .input 2], [55], #[91], 4, 99, 9) do
    throwError "bad setup failed sampling, public-key multiplication, or retained challenge"
  unless execute bad changedInput [3, 3, 55] == some (#[57, 3, 13, 17] ++ badEmpty,
      [.output 3, .invoke, .input 3, .input 3], [55], #[91], 4, 99, 9) do
    throwError "bad setup failed with a different runtime challenge and scalar"
  unless execute bad goodInput [3, 0, 55] == some (#[0, 0, 3, 5] ++ badEmpty,
      [.output 3, .invoke, .input 3, .input 0], [55], #[91], 4, 99, 9) do
    throwError "bad setup incorrectly excluded the zero scalar"
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``BLSInitialization.code, ``BLSInitialization.time, ``BLSInitialization.words, ``BLSInitialization.names,
      ``BLSInitialization.reserved, ``BLSInitialization.implementation_bounded, ``BLSSetup.good, ``BLSSetup.badLocal,
      ``BLSSetup.good_bounded, ``BLSSetup.badLocal_bounded, ``BLSSetup.good_names, ``BLSSetup.badLocal_names,
      ``BLSSetup.sample_refines, ``BLSSetup.bad_refines, ``BLSSetup.badSource_reserved, ``BLSSetup.badSource_uniform,
      ``BLSSetup.good_observe, ``BLSSetup.bad_observe, ``BLSSetup.good_time, ``BLSSetup.good_words,
      ``BLSSetup.bad_time, ``BLSSetup.bad_words, ``BLSSetup.bad_names, ``BLSSetup.bad_descriptionFits, ``BLSSetup.bad_resources,
      ``draw_correct, ``draw_law, ``good_reserved, ``bad_reserved, ``good_source, ``bad_source,
      ``good_time, ``good_words, ``bad_time, ``bad_words, ``bad_fits, ``bad_memory] do
    for dependency in (← collectAxioms name) do
      unless dependency ∈ allowed do throwError "unexpected axiom {dependency} in {name}"

end SignaturesTest.CaliperBLSSetup
