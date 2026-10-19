import Signatures.Runtime.Caliper.BLSCallerPacketBounds
import Lean

open Caliper Signatures.Runtime.CaliperBackend BoundedSource

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
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``SumContext.merge, ``SumContext.merge_time, ``SumContext.merge_words, ``SumContext.merge_names,
      ``BLSCallerPackets.prepare, ``BLSCallerPackets.finish, ``BLSCallerPackets.request_bytes,
      ``BLSCallerPackets.prepare_time, ``BLSCallerPackets.prepare_words, ``BLSCallerPackets.prepare_names,
      ``BLSCallerPackets.finish_time, ``BLSCallerPackets.finish_words, ``BLSCallerPackets.finish_names, ``prepared_bytes] do
    let axioms ← collectAxioms name
    for dependency in axioms do
      unless dependency ∈ allowed do throwError "unexpected axiom {dependency} in {name}"

end SignaturesTest.CaliperBLSPackets
