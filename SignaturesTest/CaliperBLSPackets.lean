import Signatures.Runtime.Caliper.BLSCallerInvariant
import Lean

open Caliper OracleComp OracleSpec Signatures.Runtime Signatures.Runtime.CaliperBackend BoundedSource

namespace SignaturesTest.CaliperBLSPackets

-- An infinite source message type, represented only on its admitted word range.
private def cache : CacheLayout 10 Nat (Fin 4) where
  key := Layout.counter 10 1024 (by decide) (by decide)
  value := Layout.all (Representation.fin 10 4 (by decide) (by decide))
  capacityPred := 1
  wordFits := by decide
  countFits := by decide
  storageFits := by decide
private def layout : BLSReply.Layouts 10 Nat (Fin 4) Unit (Word 10) where
  cache := cache
  point := Layout.all (wordRepresentation 10 (by decide))
  config := Layout.all (Pairing.unitRepresentation 10)
  capacityPred := 1
  countFits := by decide
  storageFits := by decide
private def default : cache.value.Value := ⟨0, trivial⟩
private def saved : layout.store.Value := ⟨((), [(5, 2)], [(5, 123)], [(6, 456)]), by
  dsimp only [BLSReply.Layouts.store, BLSReply.Layouts.cacheLogs, BLSReply.Layouts.records,
    BLSRecord.Layouts.transcript, BLSRecord.Layouts.log, BLSRecord.Layouts.entry,
    Layout.prod, Layout.boundedList, Layout.counter, Layout.all,
    CacheLayout.lookup, LookupLayout.table, LookupLayout.entry, layout, cache]
  decide⟩
private def input := BLSCallerPackets.input layout 3 (by decide)
private def prepare := BLSCallerPackets.prepare layout 3 (by decide)
private def finish := BLSCallerPackets.finish layout 3 (by decide)
private def randomRequest : BLSCallerPackets.Packet layout 3 := (.inl 3, saved)
private def hashRequest : BLSCallerPackets.Packet layout 3 := (.inr (.inl ⟨5, by change 5 < 1024; decide⟩), saved)
private def signRequest : BLSCallerPackets.Packet layout 3 := (.inr (.inr ⟨6, by change 6 < 1024; decide⟩), saved)
private def randomReply : (UniformQuery.Reply 3 × layout.store.Value) ⊕ layout.output.Value := .inl (⟨3, 2⟩, saved)
private def groupReply : (UniformQuery.Reply 3 × layout.store.Value) ⊕ layout.output.Value :=
  .inr ⟨(123, saved.val), trivial, saved.property⟩

private theorem prepared_bytes (value) (valid : BLSCallerPackets.ready layout default 3 value) :
    (BLSOracle.input layout default 3 (by decide)).encoding.encode (BLSCallerPackets.serviceRequest layout default 3 value valid) =
      (BLSCallerPackets.raw layout 3 (by decide)).encoding.encode (BLSCallerPackets.prepared layout 3 value) :=
  BLSCallerPackets.request_bytes layout default 3 (by decide) value valid
example : BLSCallerPackets.ready layout default 3 randomRequest := trivial
example : BLSCallerPackets.ready layout default 3 hashRequest := by
  dsimp [BLSCallerPackets.ready, hashRequest, saved, default, BLSReply.Layouts.guard, layout, cache, CacheLayout.admissible]
  decide
example : BLSCallerPackets.ready layout default 3 signRequest := by
  dsimp [BLSCallerPackets.ready, signRequest, saved, default, BLSReply.Layouts.guard, layout, cache, CacheLayout.admissible]
  decide

-- Finite cache/log capacity is a real precondition. A full signing transcript
-- does not become ready just because the requested key is already cached.
private def full : layout.store.Value := ⟨((), [(5, 2)], [], [(5, 123), (6, 456)]), by
  dsimp only [BLSReply.Layouts.store, BLSReply.Layouts.cacheLogs, BLSReply.Layouts.records,
    BLSRecord.Layouts.transcript, BLSRecord.Layouts.log, BLSRecord.Layouts.entry,
    Layout.prod, Layout.boundedList, Layout.counter, Layout.all,
    CacheLayout.lookup, LookupLayout.table, LookupLayout.entry, layout, cache]
  decide⟩
example : ¬ BLSCallerPackets.ready layout default 3 (.inr (.inr ⟨5, by change 5 < 1024; decide⟩), full) := by
  dsimp [BLSCallerPackets.ready, full, default, BLSReply.Layouts.guard, layout, cache, CacheLayout.admissible]
  decide

example (value) : prepare.time value ≤ 1286 := BLSCallerPackets.prepare_time layout 3 (by decide) value
example (value) : finish.time value ≤ 882 := BLSCallerPackets.finish_time layout 3 (by decide) value
example : descriptionWords prepare.code ≤ 8670 := BLSCallerPackets.prepare_words layout 3 (by decide)
example : descriptionWords finish.code ≤ 5863 := BLSCallerPackets.finish_words layout 3 (by decide)
example : NamesAccounted prepare.code 3 := BLSCallerPackets.prepare_names layout 3 (by decide)
example : NamesAccounted finish.code 3 := BLSCallerPackets.finish_names layout 3 (by decide)
example : DescriptionFits prepare.code := prepare.description_fits
example : DescriptionFits finish.code := finish.description_fits

private def base (_ : Unit) : Type := Fin 4
private instance : SampleableType (Ty.Value base (.atom ())) := inferInstanceAs (SampleableType (Fin 4))
private inductive Op : Ty Unit → Ty Unit → Type
  | equal : Op (.pair .nat .nat) .bool
private def primitives : Primitives base Op where
  execute instruction := match instruction with | .equal => fun value => decide (value.1 = value.2)
  cost _ _ := 1
private def comparison : Expr Op [.nat, .nat] .bool := .op .equal (.pair (.var .here) (.var (.there .here)))
private theorem comparison_correct (left right : Nat) : comparison.denote primitives (left, right, ()) = decide (left = right) := rfl

private def port := UniformQuery.port (w := 10) 3 (by decide) (by decide)
private def drawRequest : Realizer .unit cache.lookup.unit.representation port.request (fun _ => (3 : Fin 4)) :=
  (Implementation.constant cache.lookup.unit (Layout.all port.request) ⟨(3 : Fin 4), trivial⟩ (by decide)).program.viewOutput
    port.request (fun _ => (3 : Fin 4)) (fun _ => rfl)
private def drawValue (value : UniformQuery.Reply 3) : cache.value.Value :=
  ⟨⟨value.2.val, by have := value.1.isLt; have := value.2.isLt; omega⟩, trivial⟩
private def drawReply : Realizer .unit port.reply cache.value.representation drawValue :=
  selectSliceRealizer .unit (by decide) _ _ _ 1 (by decide) (by decide) (fun _ => rfl)
private def draw : Interactive.Code 10 := .seq (.compute drawRequest.code) (.seq .query (.compute drawReply.code))
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
    (by intro value; change (selectSlice (w := 10) 1 1).staticTime .unit ≤ 8; decide)
  exact first.seq (Interactive.Refines.compute port .unit drawRequest)
    ((UniformQuery.time_bound 3 (by decide) (by decide)).seq (UniformQuery.refines 3 (by decide) (by decide)) last)
private theorem draw_words : (draw.lower port).descriptionWords ≤ 200 := by decide
private theorem draw_names : WordIO.NamesBound (draw.lower port) 3 := by constructor <;> decide
private theorem draw_fits : (draw.lower port).DescriptionFits :=
  .seq (by decide) (.compute drawRequest.description_fits)
    (.seq (by decide) (UniformQuery.descriptionFits 3 (by decide) (by decide)) (.compute drawReply.description_fits))

-- A small actual response routine tests composition; it is not a curve library.
private def response : Implementation .unit layout.responseInput layout.point
    (fun value => BitVec.ofNat 10 value.1.val) where
  preserves _ _ := trivial
  program := selectSliceRealizer .unit (by decide) _ _ _ 0 (by decide) (by decide) (fun _ => rfl)
private theorem response_bound : response.BoundedBy 8 100 := by
  constructor
  · intro value
    change (selectSlice (w := 10) 0 1).staticTime .unit ≤ 8
    decide
  · decide
private theorem response_buffers : response.program.code.memBound ≤ 3 := by decide
private theorem response_names : NamesAccounted response.program.code 3 := selectSlice_names 0 1 3
private def handler := BLSCallerHandler.code (base := base) (key := .nat) (val := .atom ()) layout default 3 (by decide)
  primitives comparison comparison_correct (fun _ => response) (fun _ => response_buffers) (by decide) draw
private def handlerSource := BLSCallerHandler.denote (base := base) (key := .nat) (val := .atom ()) layout default 3
  primitives comparison comparison_correct (fun _ => response) (fun _ => response_buffers) (by decide) drawSource
private theorem handler_refines : Interactive.RefinesOn (BLSCallerPackets.ready layout default 3) port .unit input
    (BLSCallerPackets.output layout 3 (by decide)) handlerSource handler :=
  BLSCallerHandler.refines (base := base) (key := .nat) (val := .atom ()) layout default 3 (by decide)
    primitives comparison comparison_correct (fun _ => response) (fun _ => response_buffers) (by decide) draw draw_correct
example : Interactive.TimeBoundOn (BLSCallerPackets.ready layout default 3) port .unit input handler
    (BLSOracle.timeBudget layout (BLSDispatch.timeBudget (base := base) (key := .nat) (val := .atom ()) layout 26 (fun _ => 8)) + 2168) :=
  BLSCallerHandler.time (base := base) (key := .nat) (val := .atom ()) layout default 3 (by decide)
    primitives comparison comparison_correct (fun _ => response) (fun _ => response_buffers) (by decide) draw draw_correct draw_time (fun _ => response_bound)
example : (handler.lower port).descriptionWords ≤
    BLSOracle.codeBudget layout (BLSDispatch.codeBudget (base := base) (key := .nat) (val := .atom ()) layout 200 (fun _ => 100)) + 14620 :=
  BLSCallerHandler.words (base := base) (key := .nat) (val := .atom ()) layout default 3 (by decide)
    primitives comparison comparison_correct (fun _ => response) (fun _ => response_buffers) (by decide) draw draw_words (fun _ => response_bound)
example : WordIO.NamesAccounted (handler.lower port) 5 := by
  have bounded := BLSCallerHandler.names (base := base) (key := .nat) (val := .atom ())
    (drawSlots := 3) (responseSlots := 3) layout default 3 (by decide)
    primitives comparison comparison_correct (fun _ => response) (fun _ => response_buffers) (by decide) draw draw_names (fun _ => response_names)
  exact bounded
example : (handler.lower port).DescriptionFits :=
  BLSCallerHandler.descriptionFits (base := base) (key := .nat) (val := .atom ()) layout default 3 (by decide)
    primitives comparison comparison_correct (fun _ => response) (fun _ => response_buffers) (by decide) draw draw_fits draw_names (by decide)

private theorem handler_source (value) (valid : BLSCallerPackets.ready layout default 3 value) :
    BLSCallerHandler.observed layout 3 <$> handlerSource value =
      (fun out : (Model.LazyAGM.advSpec Nat Nat (Word 10)).Range (BLSCallerHandler.query layout 3 value.1) ×
          BLSReply.Store Nat (Fin 4) Unit (Word 10) => (BLSCallerHandler.answer layout 3 value.1 out.1, out.2)) <$>
        ((BLSCallerHandler.original (base := base) (key := .nat) (val := .atom ())
          (fun _ value => BitVec.ofNat 10 value.1.val)) (BLSCallerHandler.query layout 3 value.1)).run value.2.val :=
  BLSCallerHandler.denote_source (base := base) (key := .nat) (val := .atom ()) layout default 3
    primitives comparison comparison_correct (fun _ => response) (fun _ => response_buffers) (by decide) drawSource draw_law value valid
private theorem handler_preserves (value) {remaining : Nat} (reserved : BLSReply.Reserved layout (remaining + 1) value.2.val)
    (reply) (supported : reply ∈ support (handlerSource value)) : BLSReply.Reserved layout remaining reply.2.val :=
  BLSCallerHandler.reserved_after (base := base) (key := .nat) (val := .atom ()) layout default 3
    primitives comparison comparison_correct (fun _ => response) (fun _ => response_buffers) (by decide) drawSource draw_law value reserved reply supported

private def execute {A B : Type} {source : Representation 10 A} {target : Representation 10 B} {f : A → B}
    (program : Realizer .unit source target f) (value : A) :=
  let initial := source.initial value
  let before := { initial with bufs := fun b => if b = 200 then #[91] else initial.bufs b
                               caps := fun b => if b = 200 then 4 else initial.caps b
                               regs := fun r => if r = 200 then 99 else initial.regs r
                               tapePos := 9 }
  (WordIO.run .unit RandomTape.zero 30000 (.compute program.code) before [55]).map
    (fun finished => (finished.state.bufs 0, finished.trace, finished.remaining,
      finished.state.bufs 200, finished.state.caps 200, finished.state.regs 200, finished.state.tapePos))

private def executeHandler (value : BLSCallerPackets.Packet layout 3) (replies : List (Word 10)) :=
  let initial := input.initial value
  let before := { initial with bufs := fun b => if b = 200 then #[91] else initial.bufs b
                               caps := fun b => if b = 200 then 4 else initial.caps b
                               regs := fun r => if r = 200 then 99 else initial.regs r
                               tapePos := 9 }
  (WordIO.run .unit RandomTape.zero 100000 (handler.lower port) before replies).map
    (fun finished => (finished.state.bufs 0, finished.trace, finished.remaining,
      finished.state.bufs 200, finished.state.caps 200, finished.state.regs 200, finished.state.tapePos))

open Lean in
run_cmd do
  let stored : Array (Word 10) := #[1, 5, 2, 0, 0, 1, 5, 123, 0, 0, 1, 6, 456, 0, 0]
  unless execute prepare randomRequest == some (#[0, 3] ++ stored ++ #[0], [], [55], #[91], 4, 99, 9) do
    throwError "random request did not move padding past the private store"
  unless execute prepare hashRequest == some (#[1, 0, 5] ++ stored, [], [55], #[91], 4, 99, 9) do
    throwError "hash request lost its tag, message or private store"
  unless execute prepare signRequest == some (#[1, 1, 6] ++ stored, [], [55], #[91], 4, 99, 9) do
    throwError "signing request lost its tag, message or private store"
  unless execute finish randomReply == some (#[0, 3, 2] ++ stored, [], [55], #[91], 4, 99, 9) do
    throwError "random reply failed to retain its range, answer or private store"
  unless execute finish groupReply == some (#[1, 123, 0] ++ stored, [], [55], #[91], 4, 99, 9) do
    throwError "group reply did not move padding before the private store"
  unless executeHandler randomRequest [3, 2, 55] == some (#[0, 3, 2] ++ stored,
      [.output 3, .invoke, .input 3, .input 2], [55], #[91], 4, 99, 9) do
    throwError "composed random handler failed its request/reply/store correspondence"
  unless executeHandler hashRequest [55] == some (#[1, 2, 0, 1, 5, 2, 0, 0, 2, 5, 2, 5, 123, 1, 6, 456, 0, 0],
      [], [55], #[91], 4, 99, 9) do
    throwError "composed hash hit changed its cached sample or lost its transcript"
  unless executeHandler signRequest [3, 3, 55] == some (#[1, 3, 0, 2, 6, 3, 5, 2, 1, 5, 123, 0, 0, 2, 6, 3, 6, 456],
      [.output 3, .invoke, .input 3, .input 3], [55], #[91], 4, 99, 9) do
    throwError "composed signing miss failed sampling, insertion or recording"
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``SumContext.merge, ``SumContext.merge_time, ``SumContext.merge_words, ``SumContext.merge_names,
      ``BLSCallerPackets.prepare, ``BLSCallerPackets.finish, ``BLSCallerPackets.request_bytes,
      ``BLSCallerPackets.prepare_time, ``BLSCallerPackets.prepare_words, ``BLSCallerPackets.prepare_names,
      ``BLSCallerPackets.finish_time, ``BLSCallerPackets.finish_words, ``BLSCallerPackets.finish_names, ``prepared_bytes,
      ``Synchronizes.of_map_eq, ``Synchronizes.iff_map_eq, ``BLSCallerHandler.refines, ``BLSCallerHandler.time,
      ``BLSCallerHandler.words, ``BLSCallerHandler.names, ``BLSCallerHandler.descriptionFits,
      ``BLSCallerHandler.denote_source, ``BLSCallerHandler.synchronizes, ``BLSCallerHandler.ready_of_reserved,
      ``BLSCallerHandler.reserved_after, ``draw_correct, ``draw_law, ``handler_refines, ``handler_source, ``handler_preserves] do
    let axioms ← collectAxioms name
    for dependency in axioms do
      unless dependency ∈ allowed do throwError "unexpected axiom {dependency} in {name}"

end SignaturesTest.CaliperBLSPackets
