import Signatures.Runtime.Caliper.BLSReplySchemes
import Lean

open Caliper OracleComp OracleSpec Signatures.Runtime Signatures.Runtime.CaliperBackend
open Signatures.Runtime.CaliperBackend.BoundedSource

namespace SignaturesTest.CaliperBLSReply

private def base (_ : Unit) : Type := Fin 4
private instance : SampleableType (Ty.Value base (.atom ())) := inferInstanceAs (SampleableType (Fin 4))
private inductive Op : Ty Unit → Ty Unit → Type
  | equal : Op (.pair .nat .nat) .bool
private def primitives : Primitives base Op where
  execute instruction := match instruction with | .equal => fun value => decide (value.1 = value.2)
  cost _ _ := 1
private def comparison : Expr Op [.nat, .nat] .bool := .op .equal (.pair (.var .here) (.var (.there .here)))
private theorem comparison_correct (left right : Nat) :
    comparison.denote primitives (left, right, ()) = decide (left = right) := rfl

-- The key domain is infinite. Only messages actually used by this client fit.
private def cache : CacheLayout 10 Nat (Fin 4) where
  key := Layout.counter 10 1024 (by decide) (by decide)
  value := Layout.all (Representation.fin 10 4 (by decide) (by decide))
  capacityPred := 1
  wordFits := by decide
  countFits := by decide
  storageFits := by decide

private def replyView : (Σ _ : cache.lookup.unit.Value, Fin 4) ≃ cache.value.Value where
  toFun packet := ⟨packet.2, trivial⟩
  invFun value := ⟨⟨(), trivial⟩, value.val⟩
  left_inv packet := by rcases packet with ⟨⟨position, valid⟩, answer⟩; cases position; rfl
  right_inv _ := rfl
private def port : Interactive.Port 10 unifSpec where
  Request := cache.lookup.unit.Value
  source _ := 3
  request := cache.lookup.unit.representation
  reply := cache.value.representation.transport replyView
private noncomputable def drawSource : ProbComp cache.value.Value :=
  (fun value => ⟨value, trivial⟩) <$> ($ᵗ (Fin 4) : ProbComp (Fin 4))
private def draw : Interactive.Code 10 := .query

-- This law is for the ideal uniform-query interface, not a fair-bit tape sampler.
private theorem draw_law : Subtype.val <$> drawSource = ($ᵗ (Fin 4) : ProbComp (Fin 4)) := by
  simp [drawSource, Functor.map_map]
private theorem draw_correct : Interactive.Refines port .unit cache.lookup.unit.representation cache.value.representation
    (fun _ => drawSource) draw := by
  have projected := (Interactive.Refines.query port .unit).viewOutput cache.value.representation replyView (fun _ => rfl)
  convert projected using 1 <;> rfl


private instance : SMul (Fin 4) (Word 10) := ⟨fun scalar point => BitVec.ofNat 10 scalar.val * point⟩

private instance : SMul (Ty.Value base (.atom ())) (Word 10) := inferInstanceAs (SMul (Fin 4) (Word 10))

private def layout : BLSReply.SchemeLayouts 10 Nat (Fin 4) (Word 10) where
  cache := cache
  point := Layout.all (wordRepresentation 10 (by decide))
  responseFits := by decide
  capacityPred := 1
  countFits := by decide
  goodFits := by decide
  pairFits := by decide
  badFits := by decide

private def scale : Implementation .unit layout.response.scaleArgs layout.point (fun value => value.1 • value.2) where
  preserves _ _ := trivial
  program := ((WordBinary.realizer .unit .mul layout.cache.wordFits).viewInput layout.response.scaleArgs.representation
    (fun value => (BitVec.ofNat 10 value.val.1.val, value.val.2)) (fun _ => rfl)).viewOutput layout.point.representation
      (fun value => ⟨value.val.1 • value.val.2, trivial⟩) (fun _ => rfl)

private def add : Implementation .unit layout.response.points layout.point (fun value => value.1 + value.2) where
  preserves _ _ := trivial
  program := ((WordBinary.realizer .unit .add layout.cache.wordFits).viewInput layout.response.points.representation
    (fun value => value.val) (fun _ => rfl)).viewOutput layout.point.representation
      (fun value => ⟨value.val.1 + value.val.2, trivial⟩) (fun _ => rfl)

private theorem scale_bound : scale.BoundedBy 6 27 := ⟨fun _ => le_rfl, by decide⟩
private theorem add_bound : add.BoundedBy 6 27 := ⟨fun _ => le_rfl, by decide⟩
private theorem scale_names : NamesBound scale.program.code 3 := by constructor <;> decide
private theorem add_names : NamesBound add.program.code 3 := by constructor <;> decide
private theorem reserve : 3 + 5 < 2 ^ 10 := by decide
private def default : cache.value.Value := ⟨0, trivial⟩

private def good (signing : Bool) := BLSReply.goodCode (base := base) (key := .nat) (val := .atom ())
  layout default signing primitives comparison comparison_correct port draw scale scale_names.buffers reserve
private def bad (signing : Bool) := BLSReply.badCode (base := base) (key := .nat) (val := .atom ())
  layout default signing primitives comparison comparison_correct port draw scale scale_names.buffers reserve add add_names.buffers

private theorem draw_time : Interactive.TimeBound port .unit cache.lookup.unit.representation draw 4 := Interactive.TimeBound.query
private theorem draw_words : (draw.lower port).descriptionWords ≤ 20 := by decide
private theorem draw_names : WordIO.NamesBound (draw.lower port) 3 := by constructor <;> decide
private theorem draw_fits : (draw.lower port).DescriptionFits :=
  WordIO.exchange_descriptionFits (w := 10) 0 1 (by decide) (by decide)

example (signing : Bool) : Interactive.TimeBound port .unit (layout.good.input 0 signing).representation (good signing)
    (BLSReply.timeBudget (base := base) (key := .nat) (val := .atom ()) layout.good 4 (BLSResponse.goodTime layout.response 6)) :=
  BLSReply.good_time (base := base) (key := .nat) (val := .atom ()) layout default signing primitives comparison comparison_correct port draw scale scale_names.buffers reserve
    draw_correct draw_time scale_bound
example (signing : Bool) : Interactive.TimeBound port .unit (layout.bad.input (0, 0) signing).representation (bad signing)
    (BLSReply.timeBudget (base := base) (key := .nat) (val := .pair (.atom ()) (.atom ())) layout.bad
      (PairSampling.timeBudget cache.value cache.value 4 4) (BLSResponse.badTime layout.response signing 6 6)) :=
  BLSReply.bad_time (base := base) (key := .nat) (val := .atom ()) layout default signing primitives comparison comparison_correct port draw scale scale_names.buffers reserve add add_names.buffers
    draw_correct draw_time scale_bound add_bound

example (signing : Bool) : ((good signing).lower port).DescriptionFits :=
  BLSReply.descriptionFits (base := base) (key := .nat) (val := .atom ()) layout.good default signing primitives comparison comparison_correct port draw _ _ _ draw_fits draw_names (by decide)
example (signing : Bool) : ((bad signing).lower port).DescriptionFits :=
  BLSReply.descriptionFits (base := base) (key := .nat) (val := .pair (.atom ()) (.atom ())) layout.bad (layout.pairDefault default) signing
    primitives comparison comparison_correct port _ _ _ _
    (PairSampling.descriptionFits cache.value cache.value cache.wordFits cache.pairValueFits port draw draw draw_fits draw_fits draw_names (by decide))
    (PairSampling.names cache.value cache.value cache.wordFits cache.pairValueFits port draw draw draw_names draw_names) (by decide)

example (signing : Bool) : ((good signing).lower port).staticWords 201 201 ≤
    5 * BLSReply.codeBudget (base := base) (key := .nat) (val := .atom ()) layout.good 20 (BLSResponse.goodWords layout.response 27) + 824 := by
  exact
    BLSReply.staticMemory (base := base) (key := .nat) (val := .atom ()) layout.good default signing primitives comparison comparison_correct port draw _ _ _ draw_words draw_names
      (BLSResponse.good_bounded layout.response scale scale_bound signing)
      (BLSResponse.good_names layout.response 3 scale scale_names.accounted signing) 201 201

example (signing : Bool) : ((bad signing).lower port).staticWords 201 201 ≤
    5 * BLSReply.codeBudget (base := base) (key := .nat) (val := .pair (.atom ()) (.atom ())) layout.bad
      215 (BLSResponse.badWords layout.response signing 27 27) + 824 :=
  BLSReply.staticMemory (base := base) (key := .nat) (val := .pair (.atom ()) (.atom ())) layout.bad (layout.pairDefault default) signing
    primitives comparison comparison_correct port _ _ _ _
    (PairSampling.code_bound cache.value cache.value cache.wordFits cache.pairValueFits port draw draw draw_words draw_words)
    (PairSampling.names cache.value cache.value cache.wordFits cache.pairValueFits port draw draw draw_names draw_names)
    (BLSResponse.bad_bounded layout.response scale add scale_bound add_bound scale_names.buffers (by decide) add_names.buffers signing)
    (BLSResponse.bad_names layout.response 3 scale add scale_names.accounted add_names.accounted scale_names.buffers (by decide) add_names.buffers signing) 201 201

-- Run actual instructions, including queries. Inspect spare caller storage as well
-- as the entire output frame, so returning just the right group element is insufficient.
private structure Observation where
  output : Array (Word 10)
  trace : List (WordIO.Event 10)
  remaining : List (Word 10)
  callerWords : Array (Word 10)
  callerCapacity : Nat
  callerRegister : Word 10
  tapePosition : Nat
  deriving DecidableEq, BEq, Repr

private def execute {A : Type} (input : Layout 10 A) (value : input.Value) (program : Interactive.Code 10) (replies : List (Word 10)) : Option Observation := do
  let initial := input.representation.initial value
  let before := { initial with
    regs := fun register => if register = 200 then 99 else initial.regs register
    bufs := fun buffer => if buffer = 200 then #[77] else initial.bufs buffer
    caps := fun buffer => if buffer = 200 then 4 else initial.caps buffer
    tapePos := 9 }
  let result ← WordIO.run .unit RandomTape.zero 60000 (program.lower port) before replies
  pure ⟨result.state.bufs 0, result.trace, result.remaining, result.state.bufs 200,
    result.state.caps 200, result.state.regs 200, result.state.tapePos⟩

private def goodMiss : (layout.good.input 0 false).Value := ⟨(9, (7, 11), [], [], []), by
    dsimp only [BLSReply.Layouts.input, BLSReply.Layouts.guard, BLSReply.Layouts.plainInput,
      BLSReply.Layouts.store, BLSReply.Layouts.cacheLogs, BLSReply.Layouts.records,
      BLSReply.SchemeLayouts.good, BLSReply.SchemeLayouts.bad, BLSReply.SchemeLayouts.response,
      BLSResponse.Layouts.points, BLSResponse.Layouts.config, BLSRecord.Layouts.transcript,
      BLSRecord.Layouts.log, BLSRecord.Layouts.entry, CacheLayout.pairValues,
      Layout.prod, Layout.restrict, Layout.boundedList, Layout.counter, Layout.all,
      CacheLayout.lookup, LookupLayout.table, LookupLayout.entry, layout, cache]
    decide⟩
private def goodRepeat : (layout.good.input 0 false).Value :=
  ⟨(9, (7, 11), [(9, 3)], [(9, 21)], [(2, 22), (1, 11)]), by
    dsimp only [BLSReply.Layouts.input, BLSReply.Layouts.guard, BLSReply.Layouts.plainInput,
      BLSReply.Layouts.store, BLSReply.Layouts.cacheLogs, BLSReply.Layouts.records,
      BLSReply.SchemeLayouts.good, BLSReply.SchemeLayouts.bad, BLSReply.SchemeLayouts.response,
      BLSResponse.Layouts.points, BLSResponse.Layouts.config, BLSRecord.Layouts.transcript,
      BLSRecord.Layouts.log, BLSRecord.Layouts.entry, CacheLayout.pairValues,
      Layout.prod, Layout.restrict, Layout.boundedList, Layout.counter, Layout.all,
      CacheLayout.lookup, LookupLayout.table, LookupLayout.entry, layout, cache]
    decide⟩
private def goodSign : (layout.good.input 0 true).Value := ⟨(9, (7, 11), [(9, 3)], [(9, 21)], []), by
    dsimp only [BLSReply.Layouts.input, BLSReply.Layouts.guard, BLSReply.Layouts.plainInput,
      BLSReply.Layouts.store, BLSReply.Layouts.cacheLogs, BLSReply.Layouts.records,
      BLSReply.SchemeLayouts.good, BLSReply.SchemeLayouts.bad, BLSReply.SchemeLayouts.response,
      BLSResponse.Layouts.points, BLSResponse.Layouts.config, BLSRecord.Layouts.transcript,
      BLSRecord.Layouts.log, BLSRecord.Layouts.entry, CacheLayout.pairValues,
      Layout.prod, Layout.restrict, Layout.boundedList, Layout.counter, Layout.all,
      CacheLayout.lookup, LookupLayout.table, LookupLayout.entry, layout, cache]
    decide⟩
private def badMiss : (layout.bad.input (0, 0) false).Value := ⟨(9, (2, 7, 11), [], [], []), by
    dsimp only [BLSReply.Layouts.input, BLSReply.Layouts.guard, BLSReply.Layouts.plainInput,
      BLSReply.Layouts.store, BLSReply.Layouts.cacheLogs, BLSReply.Layouts.records,
      BLSReply.SchemeLayouts.good, BLSReply.SchemeLayouts.bad, BLSReply.SchemeLayouts.response,
      BLSResponse.Layouts.points, BLSResponse.Layouts.config, BLSRecord.Layouts.transcript,
      BLSRecord.Layouts.log, BLSRecord.Layouts.entry, CacheLayout.pairValues,
      Layout.prod, Layout.restrict, Layout.boundedList, Layout.counter, Layout.all,
      CacheLayout.lookup, LookupLayout.table, LookupLayout.entry, layout, cache]
    decide⟩
private def badSign : (layout.bad.input (0, 0) true).Value := ⟨(9, (2, 7, 11), [(9, (2, 3))], [(9, 43)], []), by
    dsimp only [BLSReply.Layouts.input, BLSReply.Layouts.guard, BLSReply.Layouts.plainInput,
      BLSReply.Layouts.store, BLSReply.Layouts.cacheLogs, BLSReply.Layouts.records,
      BLSReply.SchemeLayouts.good, BLSReply.SchemeLayouts.bad, BLSReply.SchemeLayouts.response,
      BLSResponse.Layouts.points, BLSResponse.Layouts.config, BLSRecord.Layouts.transcript,
      BLSRecord.Layouts.log, BLSRecord.Layouts.entry, CacheLayout.pairValues,
      Layout.prod, Layout.restrict, Layout.boundedList, Layout.counter, Layout.all,
      CacheLayout.lookup, LookupLayout.table, LookupLayout.entry, layout, cache]
    decide⟩

-- These operational regressions use Lean's evaluator. They are not theorem
-- assumptions; the general execution/refinement/resource proofs are checked above.
open Lean in
run_cmd do
  unless execute _ goodMiss (good false) [3, 2] == some ⟨#[21, 7, 11, 1, 9, 3, 0, 0, 1, 9, 21, 0, 0, 0, 0, 0, 0, 0], [.invoke, .input 3], [2], #[77], 4, 99, 9⟩ do
    throwError "BLS complete reply execution case 1 failed"
  unless execute _ goodRepeat (good false) [2] == some ⟨#[21, 7, 11, 1, 9, 3, 0, 0, 2, 9, 21, 9, 21, 2, 2, 22, 1, 11], [], [2], #[77], 4, 99, 9⟩ do
    throwError "BLS complete reply execution case 2 failed"
  unless execute _ goodSign (good true) [2] == some ⟨#[33, 7, 11, 1, 9, 3, 0, 0, 1, 9, 21, 0, 0, 1, 9, 33, 0, 0], [], [2], #[77], 4, 99, 9⟩ do
    throwError "BLS complete reply execution case 3 failed"
  unless execute _ badMiss (bad false) [2, 3, 1] == some ⟨#[43, 2, 7, 11, 1, 9, 2, 3, 0, 0, 0, 1, 9, 43, 0, 0, 0, 0, 0, 0, 0], [.invoke, .input 2, .invoke, .input 3], [1], #[77], 4, 99, 9⟩ do
    throwError "BLS complete reply execution case 4 failed"
  unless execute _ badSign (bad true) [1] == some ⟨#[86, 2, 7, 11, 1, 9, 2, 3, 0, 0, 0, 1, 9, 43, 0, 0, 1, 9, 86, 0, 0], [], [1], #[77], 4, 99, 9⟩ do
    throwError "BLS complete reply execution case 5 failed"

example : ¬ (layout.good.input 0 false).valid (9, (7, 11), [(9, 3)], [(9, 21), (9, 21)], []) := by
  intro valid
  have room := valid.2.2
  change 2 ≤ 1 at room
  omega
example : ¬ (layout.good.input 0 false).valid (1024, (7, 11), [], [], []) := by
    dsimp only [BLSReply.Layouts.input, BLSReply.Layouts.guard, BLSReply.Layouts.plainInput,
      BLSReply.Layouts.store, BLSReply.Layouts.cacheLogs, BLSReply.Layouts.records,
      BLSReply.SchemeLayouts.good, BLSReply.SchemeLayouts.bad, BLSReply.SchemeLayouts.response,
      BLSResponse.Layouts.points, BLSResponse.Layouts.config, BLSRecord.Layouts.transcript,
      BLSRecord.Layouts.log, BLSRecord.Layouts.entry, CacheLayout.pairValues,
      Layout.prod, Layout.restrict, Layout.boundedList, Layout.counter, Layout.all,
      CacheLayout.lookup, LookupLayout.table, LookupLayout.entry, layout, cache]
    decide

open Lean in
run_cmd do
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``BLSReply.refines, ``BLSReply.denote_source, ``BLSReply.observe,
      ``BLSReply.time_bound, ``BLSReply.code_bound, ``BLSReply.descriptionFits, ``BLSReply.memoryBound,
      ``BLSReply.good_time, ``BLSReply.bad_time, ``BLSReply.good_words, ``BLSReply.bad_words, ``BLSReply.good_observe, ``BLSReply.bad_observe,
      ``EncodedCacheRead.buffers, ``scale_bound, ``add_bound, ``draw_correct, ``draw_law] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"

end SignaturesTest.CaliperBLSReply
