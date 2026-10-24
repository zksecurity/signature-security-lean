import Proofs.Runtime.Caliper.BLSOracleSchemes
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

-- Stored request tags choose the two constructed handlers at run time.
private def goodDispatch := BLSDispatch.goodCode (base := base) (key := .nat) (val := .atom ())
  layout default primitives comparison comparison_correct port draw scale scale_names.buffers reserve
private def badDispatch := BLSDispatch.badCode (base := base) (key := .nat) (val := .atom ())
  layout default primitives comparison comparison_correct port draw scale scale_names.buffers reserve add add_names.buffers

example : Interactive.TimeBound port .unit (BLSDispatch.input layout.good default).representation goodDispatch
    (BLSDispatch.timeBudget (base := base) (key := .nat) (val := .atom ()) layout.good 4 (fun _ => BLSResponse.goodTime layout.response 6)) :=
  BLSDispatch.good_time (base := base) (key := .nat) (val := .atom ()) layout default primitives comparison comparison_correct port draw scale scale_names.buffers reserve
    draw_correct draw_time scale_bound
example : Interactive.TimeBound port .unit (BLSDispatch.input layout.bad (layout.pairDefault default)).representation badDispatch
    (BLSDispatch.timeBudget (base := base) (key := .nat) (val := .pair (.atom ()) (.atom ())) layout.bad
      (PairSampling.timeBudget cache.value cache.value 4 4) (fun signing => BLSResponse.badTime layout.response signing 6 6)) :=
  BLSDispatch.bad_time (base := base) (key := .nat) (val := .atom ()) layout default primitives comparison comparison_correct port draw scale scale_names.buffers reserve add add_names.buffers
    draw_correct draw_time scale_bound add_bound

example : (goodDispatch.lower port).descriptionWords ≤
    BLSDispatch.codeBudget (base := base) (key := .nat) (val := .atom ()) layout.good 20 (fun _ => BLSResponse.goodWords layout.response 27) :=
  BLSDispatch.good_words (base := base) (key := .nat) (val := .atom ()) layout default primitives comparison comparison_correct port draw scale scale_names.buffers reserve scale_bound draw_words
example : (badDispatch.lower port).descriptionWords ≤
    BLSDispatch.codeBudget (base := base) (key := .nat) (val := .pair (.atom ()) (.atom ())) layout.bad
      (PairSampling.codeBudget cache.value cache.value 20 20) (fun signing => BLSResponse.badWords layout.response signing 27 27) :=
  BLSDispatch.bad_words (base := base) (key := .nat) (val := .atom ()) layout default primitives comparison comparison_correct port draw scale scale_names.buffers reserve add add_names.buffers scale_bound add_bound draw_words

example : (goodDispatch.lower port).DescriptionFits :=
  BLSDispatch.descriptionFits (base := base) (key := .nat) (val := .atom ()) layout.good default primitives comparison comparison_correct port draw _ _ _ draw_fits draw_names (by decide)
example : (badDispatch.lower port).DescriptionFits :=
  BLSDispatch.descriptionFits (base := base) (key := .nat) (val := .pair (.atom ()) (.atom ())) layout.bad (layout.pairDefault default)
    primitives comparison comparison_correct port _ _ _ _
    (PairSampling.descriptionFits cache.value cache.value cache.wordFits cache.pairValueFits port draw draw draw_fits draw_fits draw_names (by decide))
    (PairSampling.names cache.value cache.value cache.wordFits cache.pairValueFits port draw draw draw_names draw_names) (by decide)

-- The same dynamic uniform port serves both adversary randomness and private
-- scalar draws. The scalar request and result projection execute word code.
private def sharedPort := UniformQuery.port (w := 10) 3 (by decide) (by decide)
private def sharedPrepare : Realizer .unit cache.lookup.unit.representation sharedPort.request (fun _ => (3 : Fin 4)) :=
  (Implementation.constant cache.lookup.unit (Layout.all sharedPort.request) ⟨(3 : Fin 4), trivial⟩ (by decide)).program.viewOutput
    sharedPort.request (fun _ => (3 : Fin 4)) (fun _ => rfl)
private def sharedValue (packet : UniformQuery.Reply 3) : Fin 4 :=
  ⟨packet.2.val, by have := packet.1.isLt; have := packet.2.isLt; omega⟩
private def sharedExtract : Realizer .unit sharedPort.reply cache.value.representation
    (fun packet => ⟨sharedValue packet, trivial⟩) :=
  ((secondRealizer .unit (by decide) (Representation.fin 10 4 (by decide) (by decide))
    (Representation.fin 10 4 (by decide) (by decide)) (by decide) (by decide)).viewInput sharedPort.reply
      (fun packet => (packet.1, sharedValue packet)) (fun _ => rfl)).viewOutput cache.value.representation
        (fun packet => ⟨sharedValue packet, trivial⟩) (fun _ => rfl)
private def sharedDraw : Interactive.Code 10 :=
  .seq (.compute sharedPrepare.code) (.seq .query (.compute sharedExtract.code))
private theorem shared_correct : Interactive.Refines sharedPort .unit cache.lookup.unit.representation cache.value.representation
    (fun _ => drawSource) sharedDraw := by
  have combined := (Interactive.Refines.compute sharedPort .unit sharedPrepare).seq
    ((Interactive.Refines.query sharedPort .unit).seq (Interactive.Refines.compute sharedPort .unit sharedExtract))
  convert combined using 1
  · funext value
    simp only [bind_pure_comp]
    rfl
  · rfl
private theorem shared_time : Interactive.TimeBound sharedPort .unit cache.lookup.unit.representation sharedDraw 26 := by
  have prepare := Interactive.TimeBound.compute (port := sharedPort) (cost := .unit) sharedPrepare 8
    (Implementation.constant_bounded cache.lookup.unit (Layout.all sharedPort.request) ⟨(3 : Fin 4), trivial⟩ (by decide)).time_le
  have finish := Interactive.TimeBound.compute (port := sharedPort) (cost := .unit) sharedExtract 8 (fun _ => by change 8 ≤ 8; decide)
  exact prepare.seq (Interactive.Refines.compute sharedPort .unit sharedPrepare)
    ((UniformQuery.time_bound 3 (by decide) (by decide)).seq (UniformQuery.refines 3 (by decide) (by decide)) finish)
private theorem shared_words : (sharedDraw.lower sharedPort).descriptionWords ≤ 125 := by decide
private theorem shared_names : WordIO.NamesBound (sharedDraw.lower sharedPort) 3 := by constructor <;> decide
private theorem shared_fits : (sharedDraw.lower sharedPort).DescriptionFits :=
  .seq (by decide) (.compute sharedPrepare.description_fits)
    (.seq (by decide) (UniformQuery.descriptionFits 3 (by decide) (by decide)) (.compute sharedExtract.description_fits))

private def goodOracle := BLSOracle.goodCode (base := base) (key := .nat) (val := .atom ())
  layout default 3 (by decide) primitives comparison comparison_correct sharedDraw scale scale_names.buffers reserve
private def badOracle := BLSOracle.badCode (base := base) (key := .nat) (val := .atom ())
  layout default 3 (by decide) primitives comparison comparison_correct sharedDraw scale scale_names.buffers reserve add add_names.buffers

example : Interactive.TimeBound sharedPort .unit (BLSOracle.input layout.good default 3 (by decide)) goodOracle
    (BLSOracle.timeBudget layout.good (BLSDispatch.timeBudget (base := base) (key := .nat) (val := .atom ()) layout.good 26 (fun _ => BLSResponse.goodTime layout.response 6))) :=
  BLSOracle.time_bound (base := base) (key := .nat) (val := .atom ()) layout.good default 3 (by decide) primitives comparison comparison_correct _ _ _ sharedDraw
    shared_correct shared_time (BLSResponse.good_bounded layout.response scale scale_bound)
example : Interactive.TimeBound sharedPort .unit (BLSOracle.input layout.bad (layout.pairDefault default) 3 (by decide)) badOracle
    (BLSOracle.timeBudget layout.bad (BLSDispatch.timeBudget (base := base) (key := .nat) (val := .pair (.atom ()) (.atom ())) layout.bad
      (PairSampling.timeBudget cache.value cache.value 26 26) (fun signing => BLSResponse.badTime layout.response signing 6 6))) :=
  BLSOracle.time_bound (base := base) (key := .nat) (val := .pair (.atom ()) (.atom ())) layout.bad (layout.pairDefault default) 3 (by decide) primitives comparison comparison_correct _ _ _ _
    (PairSampling.refines (hw := cache.wordFits) (fits := cache.pairValueFits) shared_correct shared_correct)
    (PairSampling.time_bound (hw := cache.wordFits) (fits := cache.pairValueFits) shared_correct shared_correct shared_time shared_time)
    (BLSResponse.bad_bounded layout.response scale add scale_bound add_bound scale_names.buffers (by decide) add_names.buffers)

example : (goodOracle.lower sharedPort).DescriptionFits :=
  BLSOracle.descriptionFits (base := base) (key := .nat) (val := .atom ()) layout.good default 3 (by decide)
    primitives comparison comparison_correct _ _ _ sharedDraw shared_fits shared_names (by decide)
example : (badOracle.lower sharedPort).DescriptionFits :=
  BLSOracle.descriptionFits (base := base) (key := .nat) (val := .pair (.atom ()) (.atom ())) layout.bad (layout.pairDefault default) 3 (by decide)
    primitives comparison comparison_correct _ _ _ _
    (PairSampling.descriptionFits cache.value cache.value cache.wordFits cache.pairValueFits sharedPort sharedDraw sharedDraw shared_fits shared_fits shared_names (by decide))
    (PairSampling.names cache.value cache.value cache.wordFits cache.pairValueFits sharedPort sharedDraw sharedDraw shared_names shared_names) (by decide)

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

private def execute {A : Type} (input : Layout 10 A) (value : input.Value) (program : Interactive.Code 10) (replies : List (Word 10)) (activePort : Interactive.Port 10 unifSpec := port) : Option Observation := do
  let initial := input.representation.initial value
  let before := { initial with
    regs := fun register => if register = 200 then 99 else initial.regs register
    bufs := fun buffer => if buffer = 200 then #[77] else initial.bufs buffer
    caps := fun buffer => if buffer = 200 then 4 else initial.caps buffer
    tapePos := 9 }
  let result ← WordIO.run .unit RandomTape.zero 60000 (program.lower activePort) before replies
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

-- The source theorem covers any adaptive client with this query allowance.
-- It does not enumerate or restrict the source's infinite Nat message type.
private theorem initial_reserved : BLSReply.Reserved layout.good 2 ((7, 11), [], [], []) :=
  ⟨goodMiss.property.1.2.1, goodMiss.property.1.2.2.1.2,
    ⟨goodMiss.property.1.2.2.2.1.2, goodMiss.property.1.2.2.2.2.2⟩, by decide, by decide⟩

example {A : Type} {main : OracleComp (Model.LazyAGM.advSpec Nat Nat (Word 10)) A}
    {state : LazyAGM.State Nat (Fin 4) (Word 10)} {used : Nat}
    (queries : AllQueriesSatisfy main (BLSRecord.allowedQuery layout.good.records))
    (bounded : IsTotalQueryBound main 2) (signing : Bool) (message : Nat)
    (next : (Model.LazyAGM.advSpec Nat Nat (Word 10)).Range (BLSRecord.request signing message) →
      OracleComp (Model.LazyAGM.advSpec Nat Nat (Word 10)) A)
    (path : SourcePrefix (LazyAGM.listOracle (fun rho : Fin 4 => rho • (7 : Word 10)) (fun rho : Fin 4 => rho • (11 : Word 10)))
      main ([], [], []) (queryBind (BLSRecord.request signing message) next) state used) :
    (layout.good.input 0 signing).valid (message, (7, 11), state) :=
  BLSReply.prefix_ready (base := base) (key := .nat) (val := .atom ()) layout.good default primitives comparison comparison_correct
    (BLSResponse.good layout.response scale) (BLSResponse.good_buffers layout.response scale scale_names.buffers) (layout.goodReserve reserve)
    drawSource draw_law initial_reserved queries bounded signing message next path

-- A tiny regression client reads the first reply's encoded point. A nonzero
-- reply triggers signing a fresh message; zero triggers hashing the same one.
-- Both requests keep the returned store by executing reads/copies in Caliper.
-- No host-language decoding/re-encoding occurs between these calls.
private def nextRequest (storeWords : Nat) (tag message : Word 10) : Interactive.Code 10 :=
  .compute (Assembly.code ([.literal tag, .literal message] ++ Assembly.reads 0 1 storeWords))
private def adaptive (handler : Interactive.Code 10) (storeWords : Nat) : Interactive.Code 10 :=
  .seq handler (.seq (.compute (.imm 1 0 ;; .memLoad 1 0 1))
    (.seq (.branch 1 (nextRequest storeWords 1 8) (nextRequest storeWords 0 9)) handler))

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

open Lean in
run_cmd do
  let goodInput := BLSDispatch.request layout.good default false goodMiss
  let badInput := BLSDispatch.request layout.bad (layout.pairDefault default) false badMiss
  unless execute _ goodInput (adaptive goodDispatch layout.good.store.representation.encoding.words) [3, 2, 1] ==
      some ⟨#[22, 7, 11, 2, 8, 2, 9, 3, 1, 9, 21, 0, 0, 1, 8, 22, 0, 0], [.invoke, .input 3, .invoke, .input 2], [1], #[77], 4, 99, 9⟩ do
    throwError "BLS dispatched adaptive fresh-sign case failed"
  unless execute _ goodInput (adaptive goodDispatch layout.good.store.representation.encoding.words) [0, 2] ==
      some ⟨#[0, 7, 11, 1, 9, 0, 0, 0, 2, 9, 0, 9, 0, 0, 0, 0, 0, 0], [.invoke, .input 0], [2], #[77], 4, 99, 9⟩ do
    throwError "BLS dispatched adaptive hash-hit case failed"
  unless execute _ badInput (adaptive badDispatch layout.bad.store.representation.encoding.words) [2, 3, 1, 1, 2] ==
      some ⟨#[36, 2, 7, 11, 2, 8, 1, 1, 9, 2, 3, 1, 9, 43, 0, 0, 1, 8, 36, 0, 0], [.invoke, .input 2, .invoke, .input 3, .invoke, .input 1, .invoke, .input 1], [2], #[77], 4, 99, 9⟩ do
    throwError "BLS paired dispatched adaptive fresh-sign case failed"
  unless execute _ badInput (adaptive badDispatch layout.bad.store.representation.encoding.words) [0, 0, 2] ==
      some ⟨#[0, 2, 7, 11, 1, 9, 0, 0, 0, 0, 0, 2, 9, 0, 9, 0, 0, 0, 0, 0, 0], [.invoke, .input 0, .invoke, .input 0], [2], #[77], 4, 99, 9⟩ do
    throwError "BLS paired dispatched adaptive hash-hit case failed"

-- Interleave a private hash, an adversary random query and an adaptive reply.
-- Configuration/cache/logs survive both the group and random output formats.
private def oracleRoundTrip (handler : Interactive.Code 10) (storeWords : Nat) : Interactive.Code 10 :=
  .seq handler (.seq (.compute (Assembly.code ([.literal 0, .literal 1] ++ Assembly.reads 0 2 storeWords ++ [.literal 0])))
    (.seq handler (.seq (.compute (.imm 1 2 ;; .memLoad 1 0 1))
      (.seq (.branch 1
        (.compute (Assembly.code ([.literal 1, .literal 1, .literal 9] ++ Assembly.reads 0 3 storeWords)))
        (.compute (Assembly.code ([.literal 1, .literal 0, .literal 9] ++ Assembly.reads 0 3 storeWords)))) handler))))

open Lean in
run_cmd do
  let goodInput := (Layout.all (BLSOracle.input layout.good default 3 (by decide)))
  let goodValue : goodInput.Value := ⟨.inr (BLSDispatch.request layout.good default false goodMiss), trivial⟩
  let badInput := (Layout.all (BLSOracle.input layout.bad (layout.pairDefault default) 3 (by decide)))
  let badValue : badInput.Value := ⟨.inr (BLSDispatch.request layout.bad (layout.pairDefault default) false badMiss), trivial⟩
  unless execute goodInput goodValue (oracleRoundTrip goodOracle layout.good.store.representation.encoding.words) [3, 3, 1, 1, 77] sharedPort ==
      some ⟨#[1, 33, 7, 11, 1, 9, 3, 0, 0, 1, 9, 21, 0, 0, 1, 9, 33, 0, 0, 0], [.output 3, .invoke, .input 3, .input 3, .output 1, .invoke, .input 1, .input 1], [77], #[77], 4, 99, 9⟩ do
    throwError "BLS full service hash/random/sign sequence failed"
  unless execute goodInput goodValue (oracleRoundTrip goodOracle layout.good.store.representation.encoding.words) [3, 3, 1, 0, 77] sharedPort ==
      some ⟨#[1, 21, 7, 11, 1, 9, 3, 0, 0, 2, 9, 21, 9, 21, 0, 0, 0, 0, 0, 0], [.output 3, .invoke, .input 3, .input 3, .output 1, .invoke, .input 1, .input 0], [77], #[77], 4, 99, 9⟩ do
    throwError "BLS full service hash/random/hash sequence failed"
  unless execute badInput badValue (oracleRoundTrip badOracle layout.bad.store.representation.encoding.words) [3, 2, 3, 3, 1, 1, 77] sharedPort ==
      some ⟨#[1, 86, 2, 7, 11, 1, 9, 2, 3, 0, 0, 0, 1, 9, 43, 0, 0, 1, 9, 86, 0, 0, 0], [.output 3, .invoke, .input 3, .input 2, .output 3, .invoke, .input 3, .input 3, .output 1, .invoke, .input 1, .input 1], [77], #[77], 4, 99, 9⟩ do
    throwError "BLS paired full service hash/random/sign sequence failed"
  unless (UniformQuery.reply (w := 10) 3 (by decide) (by decide)).encoding.decode [1, 2] == none do
    throwError "uniform dependent reply accepted an out-of-range sample"
  unless (UniformQuery.request (w := 10) 3 (by decide) (by decide)).encoding.decode [4] == none do
    throwError "uniform request accepted an out-of-range bound"

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
  for name in [``UniformQuery.refines, ``UniformQuery.forward_refines, ``UniformQuery.forward_time, ``UniformQuery.forward_words,
      ``UniformQuery.forward_descriptionFits, ``UniformQuery.forward_names, ``Interactive.Refines.resources,
      ``BLSOracle.refines, ``BLSOracle.denote_source, ``BLSOracle.observe, ``BLSOracle.prefix_ready,
      ``BLSOracle.time_bound, ``BLSOracle.code_bound, ``BLSOracle.descriptionFits, ``BLSOracle.memoryBound,
      ``shared_correct, ``shared_time, ``shared_words, ``shared_fits,
      ``BLSDispatch.refines, ``BLSDispatch.denote_source, ``BLSDispatch.observe,
      ``BLSDispatch.time_bound, ``BLSDispatch.code_bound, ``BLSDispatch.descriptionFits, ``BLSDispatch.memoryBound,
      ``BLSDispatch.good_time, ``BLSDispatch.bad_time, ``BLSDispatch.good_words, ``BLSDispatch.bad_words,
      ``BLSDispatch.good_observe, ``BLSDispatch.bad_observe, ``BLSDispatch.returns_reserved,
      ``BLSReply.reply_output, ``BLSReply.reply_reserved, ``BLSReply.query_reserved, ``BLSReply.prefix_reserved, ``BLSReply.prefix_ready,
      ``BLSReply.refines, ``BLSReply.denote_source, ``BLSReply.observe,
      ``BLSReply.time_bound, ``BLSReply.code_bound, ``BLSReply.descriptionFits, ``BLSReply.memoryBound,
      ``BLSReply.good_time, ``BLSReply.bad_time, ``BLSReply.good_words, ``BLSReply.bad_words, ``BLSReply.good_observe, ``BLSReply.bad_observe,
      ``EncodedCacheRead.buffers, ``scale_bound, ``add_bound, ``draw_correct, ``draw_law] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"

end SignaturesTest.CaliperBLSReply
