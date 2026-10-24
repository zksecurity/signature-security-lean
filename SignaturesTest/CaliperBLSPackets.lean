import Proofs.Runtime.Caliper.BLSCallerResources
import Proofs.Runtime.Caliper.BLSInitialization
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

-- Actual adaptive caller: a random answer selects the next hash message.
-- The local pending request is represented twice, as query and caller state.
private def requestRep := BLSCallerPackets.request layout 3 (by decide)
private def replyRep := BLSCallerPackets.reply layout 3 (by decide)
private def callerLayout := BLSCaller.layout layout 3 (by decide) requestRep layout.point.representation (by decide)
private def initial (q : BLSCallerPackets.Request layout 3) :
    layout.point.Value ⊕ (BLSCallerPackets.Request layout 3 × BLSCallerPackets.Request layout 3) := .inr (q, q)
private def initialCode : Realizer .unit requestRep (CallerStep.next callerLayout) initial :=
  ((duplicateRealizer .unit (by decide) requestRep (by decide) (by decide)).then
    (inrRealizer .unit (by decide) layout.point.representation (CallerStep.pending callerLayout)
      (by decide) (by decide))).viewOutput (CallerStep.next callerLayout) initial (fun _ => rfl)
private def randomMessage (value : UniformQuery.Reply 3) : cache.key.Value :=
  ⟨value.2.val, by change value.2.val < 1024; have := value.1.isLt; have := value.2.isLt; omega⟩
private def messageCode : Realizer .unit port.reply cache.key.representation randomMessage :=
  selectSliceRealizer .unit (by decide) _ _ _ 1 (by decide) (by decide) (fun _ => rfl)
private def hashCode := (messageCode.then
  (inlRealizer .unit (by decide) cache.key.representation cache.key.representation (by decide) (by decide))).then
    (inrRealizer .unit (by decide) port.request
      (cache.key.representation.sum cache.key.representation (by decide) (by decide)) (by decide) (by decide))
private def advance (value : BLSCallerPackets.Request layout 3 × BLSCallerPackets.Reply layout 3) :=
  match value.2 with
  | .inl random => initial (.inr (.inl (randomMessage random)))
  | .inr point => .inl point
private def continuation : Realizer .unit (CallerStep.resume callerLayout) (CallerStep.next callerLayout) advance :=
  ((secondRealizer .unit (by decide) requestRep replyRep (by decide) (by decide)).then
    (branchRealizer .unit (by decide) port.reply layout.point.representation (CallerStep.next callerLayout)
      (hashCode.then initialCode)
      (inlRealizer .unit (by decide) layout.point.representation (CallerStep.pending callerLayout) (by decide) (by decide))
      (by decide) (by decide))).viewOutput (CallerStep.next callerLayout) advance (by
        rintro ⟨pending, random | point⟩ <;> rfl)
private def localDomain (_ : Nat) (value : BLSCallerPackets.Request layout 3 × BLSCallerPackets.Request layout 3) := value.1 = value.2
private theorem advance_valid (remaining : Nat) (q c) (_ : localDomain (remaining + 1) (q, c))
    (represented) (original) (_ : BLSCallerHandler.replyMatches layout 3 q represented original) :
    BLSCaller.HeadValid layout 3 localDomain remaining (advance (c, represented)) := by
  cases represented with
  | inl random => rfl
  | inr point => trivial
private def empty : layout.store.Value := ⟨((), [], [], []), by
  dsimp only [BLSReply.Layouts.store, BLSReply.Layouts.cacheLogs, BLSReply.Layouts.records,
    BLSRecord.Layouts.transcript, BLSRecord.Layouts.log, BLSRecord.Layouts.entry,
    Layout.prod, Layout.boundedList, Layout.counter, Layout.all,
    CacheLayout.lookup, LookupLayout.table, LookupLayout.entry, layout, cache]
  decide⟩
private def callerInput := requestRep.prod layout.store.representation (by decide)
private def admitted (value : BLSCallerPackets.Request layout 3 × layout.store.Value) :=
  BLSReply.Reserved layout 2 value.2.val
private theorem initial_valid (value) (_ : admitted value) :
    BLSCaller.HeadValid layout 3 localDomain 2 (initial value.1) := rfl
private def caller (fuel : Nat) := BLSCaller.program (base := base) (key := .nat) (val := .atom ()) layout default 3 (by decide)
  primitives comparison comparison_correct (fun _ => response) (fun _ => response_buffers) (by decide) draw advance
  requestRep layout.point.representation (by decide) continuation (by decide) requestRep initial initialCode (by decide) (by decide) fuel
private theorem caller_refines : Interactive.RefinesOn admitted port .unit callerInput (CallerStep.output callerLayout)
    (fun value => CallerControl.start advance handlerSource 2 (initial value.1, value.2)) (caller 2) :=
  BLSCaller.refines (base := base) (key := .nat) (val := .atom ()) layout default 3 (by decide)
    primitives comparison comparison_correct (fun _ => response) (fun _ => response_buffers) (by decide) draw drawSource
    draw_correct draw_law localDomain advance advance_valid requestRep layout.point.representation (by decide)
    continuation (by decide) requestRep initial initialCode (by decide) (by decide) 2 admitted initial_valid (fun _ valid => valid)

private theorem caller_postcondition (tape : RandomTape 10) (value) (valid : admitted value)
    (before : State 10) (holds : callerInput.Holds value before)
    (finished : WordIO.Result 10) (reached : some finished ∈ support ((caller 2).execute port .unit tape before)) :
    ∃ answer, (CallerStep.output callerLayout).Holds answer finished.state ∧
      BLSCaller.Postcondition layout 2 value.2 answer.2 ∧
      WordIO.Exec .unit tape ((caller 2).lower port) before finished.state finished.trace finished.time finished.net finished.peak :=
  BLSCaller.execution_postcondition (base := base) (key := .nat) (val := .atom ()) layout default 3 (by decide)
    primitives comparison comparison_correct (fun _ => response) (fun _ => response_buffers) (by decide) draw drawSource
    draw_correct draw_law localDomain advance advance_valid requestRep layout.point.representation (by decide)
    continuation (by decide) requestRep initial initialCode (by decide) (by decide) 2 admitted initial_valid (fun _ valid => valid)
    tape value valid before holds finished reached

-- Extraction capacity is only needed in the private cache: five cache entries
-- and two transcript entries suffice for a two-query caller from an empty store.
private def extractionLayout : BLSReply.Layouts 10 Nat (Fin 4) Unit (Word 10) :=
  { layout with
    cache := { cache with capacityPred := 4, countFits := by decide, storageFits := by decide }
    storageFits := by decide }
private def extractionEmpty := BLSInitialization.store extractionLayout ⟨(), trivial⟩
private def extractionHandler := BLSCallerHandler.denote (base := base) (key := .nat) (val := .atom ()) extractionLayout default 3
  primitives comparison comparison_correct (fun _ => response) (fun _ => response_buffers) (by decide) drawSource
private theorem extraction_reserved : BLSReply.Reserved extractionLayout 2 extractionEmpty.val :=
  BLSInitialization.reserved extractionLayout 2 (by decide) (by decide) ⟨(), trivial⟩
example : ¬ BLSReply.Reserved extractionLayout 5 extractionEmpty.val := by
  intro reserved
  have impossible : 5 ≤ 2 := reserved.logRoom
  omega
private theorem caller_extraction_room (q : BLSCallerPackets.Request extractionLayout 3)
    (answer) (reached : answer ∈ support (CallerControl.start advance extractionHandler 2 (initial q, extractionEmpty))) :
    answer.2.val.2.1.length + (answer.2.val.2.2.1.length + answer.2.val.2.2.2.length + 1) ≤ 5 := by
  have post := BLSCaller.start_postcondition (base := base) (key := .nat) (val := .atom ()) extractionLayout default 3
    primitives comparison comparison_correct (fun _ => response) (fun _ => response_buffers) (by decide) drawSource draw_law
    advance 2 (initial q, extractionEmpty) extraction_reserved answer reached
  exact post.extraction_room (by change 5 ≤ 5; decide)

private abbrev SourceSpec := Model.LazyAGM.advSpec Nat Nat (Word 10)
private def sourceNext : (q : SourceSpec.Domain) → SourceSpec.Range q → layout.point.Value ⊕ SourceSpec.Domain
  | .inl (.inl _), random => .inr (.inl (.inr random.val))
  | .inl (.inr _), point | .inr _, point => .inl ⟨point, trivial⟩
private def machineStep (value : layout.point.Value ⊕ SourceSpec.Domain) :
    layout.point.Value ⊕ SourceSpec.toPFunctor.Obj (layout.point.Value ⊕ SourceSpec.Domain) :=
  match value with
  | .inl point => .inl point
  | .inr q => .inr ⟨q, sourceNext q⟩
private def machine : OracleMachine SourceSpec SourceSpec.Domain layout.point.Value :=
  PFunctor.DynSystem.DynComputation.ofStep machineStep Sum.inr
private def sourceProgram : SourceSpec.Domain → OracleComp SourceSpec layout.point.Value
  | .inl (.inl n) => do
      let random ← SourceSpec.query (.inl (.inl n))
      let point ← SourceSpec.query (.inl (.inr random.val))
      pure ⟨point, trivial⟩
  | .inl (.inr message) => do
      let point ← SourceSpec.query (.inl (.inr message))
      pure ⟨point, trivial⟩
  | .inr message => do
      let point ← SourceSpec.query (.inr message)
      pure ⟨point, trivial⟩
private theorem caller_implements : machine.ImplementsWithin sourceProgram 2 := by
  intro q
  rcases q with (n | message) | message <;>
    simp [machine, sourceProgram, PFunctor.DynSystem.DynComputation.run,
      PFunctor.DynSystem.DynComputation.unroll, machineStep, sourceNext, bind_pure_comp] <;> rfl
private def stateView (value : BLSCallerPackets.Request layout 3 × BLSCallerPackets.Request layout 3) : machine.State :=
  .inr (BLSCallerHandler.query layout 3 value.2)
private theorem advance_matches (remaining : Nat) (q c) (valid : localDomain (remaining + 1) (q, c))
    (next : SourceSpec.Range (BLSCallerHandler.query layout 3 q) → machine.State)
    (view : machine.view (stateView (q, c)) = .inr ⟨BLSCallerHandler.query layout 3 q, next⟩)
    (represented original) (related : BLSCallerHandler.replyMatches layout 3 q represented original) :
    CallerMachine.Matches machine (BLSCallerHandler.query layout 3) stateView (advance (c, represented)) (next original) := by
  change q = c at valid
  subst c
  rw [machine.next_eq_of_view_query view (show machine.view (stateView (q, q)) =
    .inr ⟨BLSCallerHandler.query layout 3 q, sourceNext (BLSCallerHandler.query layout 3 q)⟩ from rfl)]
  rcases q with n | (message | message)
  · cases represented with
    | inl random =>
      have equal : random.2.val = original.val := (Prod.mk.inj (Sum.inl.inj related)).2
      change CallerMachine.Matches machine (BLSCallerHandler.query layout 3) stateView (initial (.inr (.inl (randomMessage random))))
        (.inr (.inl (.inr original.val)))
      rw [← equal]
      exact .pending _ _ (sourceNext (.inl (.inr random.2.val))) rfl
    | inr point => cases related
  · cases represented with
    | inl random => cases related
    | inr point =>
      have equal : point.val = original := Sum.inr.inj related
      apply CallerMachine.Matches.returned
      change Sum.inl (⟨original, trivial⟩ : layout.point.Value) = Sum.inl point
      congr 1
      exact Subtype.ext equal.symm
  · cases represented with
    | inl random => cases related
    | inr point =>
      have equal : point.val = original := Sum.inr.inj related
      apply CallerMachine.Matches.returned
      change Sum.inl (⟨original, trivial⟩ : layout.point.Value) = Sum.inl point
      congr 1
      exact Subtype.ext equal.symm
private theorem initial_matches (value) (_ : admitted value) :
    CallerMachine.Matches machine (BLSCallerHandler.query layout 3) stateView (initial value.1)
      (machine.init (BLSCallerHandler.query layout 3 value.1)) :=
  .pending _ _ (sourceNext (BLSCallerHandler.query layout 3 value.1)) rfl
private theorem caller_source (tape : RandomTape 10) (value) (valid : admitted value)
    (before : State 10) (holds : callerInput.Holds value before) :
    (fun finished => CallerMachine.observe Subtype.val <$> Interactive.observe (CallerStep.output callerLayout) finished) <$>
      (caller 2).execute port .unit tape before =
      (fun finished => some (some finished.1, finished.2)) <$>
        (simulateQ (BLSCallerHandler.original (base := base) (key := .nat) (val := .atom ())
          (fun _ value => BitVec.ofNat 10 value.1.val)) (sourceProgram (BLSCallerHandler.query layout 3 value.1))).run value.2.val :=
  BLSCaller.observe_source (base := base) (key := .nat) (val := .atom ()) layout default 3 (by decide)
    primitives comparison comparison_correct (fun _ => response) (fun _ => response_buffers) (by decide) draw drawSource
    draw_correct draw_law localDomain advance advance_valid requestRep layout.point.representation (by decide)
    continuation (by decide) requestRep initial initialCode (by decide) (by decide) 2 admitted initial_valid (fun _ valid => valid)
    machine stateView (BLSCallerHandler.query layout 3) advance_matches initial_matches sourceProgram caller_implements tape value valid before holds

private theorem empty_admitted (q) : admitted (q, empty) := by
  constructor
  · trivial
  · intro entry member
    cases member
  · constructor <;> intro entry member <;> cases member
  · change 2 ≤ 2
    decide
  · change 2 ≤ 2
    decide
private theorem continuation_time (value) : continuation.time value ≤ 1000 := by
  rcases value with ⟨pending, random | point⟩
  · change continuation.time (.inl 0, .inl ⟨(0 : Fin 4), (0 : Fin 1)⟩) ≤ 1000
    decide
  · change continuation.time (.inl 0, .inr ⟨0, trivial⟩) ≤ 1000
    decide
private theorem initial_time (value) : initialCode.time value ≤ 1000 := by
  change initialCode.time (.inl 0) ≤ 1000
  decide
-- Expose the small instruction trees before evaluating their numerical profiles;
-- this keeps representation proof terms out of arithmetic normalization.
private def initialRaw : Stmt 10 :=
  Assembly.code (Assembly.reads 0 0 3 ++ Assembly.reads 0 0 3) ;;
    Assembly.code (Construction.taggedOperands 1 6 0)
private def continuationRaw : Stmt 10 :=
  selectSlice 3 3 ;; Dispatch.code
    (((selectSlice 1 1 ;; Assembly.code (Construction.taggedOperands 0 1 0)) ;;
      Assembly.code (Construction.taggedOperands 1 2 0)) ;; initialRaw)
    (Assembly.code (Construction.taggedOperands 0 1 5)) 2 1
private theorem initial_code : initialCode.code = initialRaw := rfl
private theorem continuation_code : continuation.code = continuationRaw := rfl
private theorem initial_words : descriptionWords initialCode.code ≤ 5000 := by
  have copied := Assembly.code_descriptionWords_le (Assembly.reads (w := 10) 0 0 3 ++ Assembly.reads 0 0 3)
  have tagged := Assembly.code_descriptionWords_le (Construction.taggedOperands (w := 10) 1 6 0)
  simp only [List.length_append, Assembly.reads_length, Construction.prefix_length] at copied tagged
  rw [initial_code, initialRaw, descriptionWords_seq]
  omega
private theorem continuation_words : descriptionWords continuation.code ≤ 5000 := by
  have copied := Assembly.code_descriptionWords_le (Assembly.reads (w := 10) 0 0 3 ++ Assembly.reads 0 0 3)
  have tagged := Assembly.code_descriptionWords_le (Construction.taggedOperands (w := 10) 1 6 0)
  have first := Assembly.code_descriptionWords_le (Construction.taggedOperands (w := 10) 0 1 0)
  have second := Assembly.code_descriptionWords_le (Construction.taggedOperands (w := 10) 1 2 0)
  have last := Assembly.code_descriptionWords_le (Construction.taggedOperands (w := 10) 0 1 5)
  simp only [List.length_append, Assembly.reads_length, Construction.prefix_length] at copied tagged first second last
  simp only [continuation_code, continuationRaw, initialRaw, descriptionWords_seq,
    Dispatch.code_descriptionWords, selectSlice_descriptionWords]
  omega
private theorem initial_names : NamesAccounted initialCode.code 5 := by
  rw [initial_code]
  exact (Assembly.code_namesAccounted _ 5 ((Assembly.sourcesBound_append _ _ _).mpr
    ⟨Assembly.sourcesBound_reads _ _ _ _ (by decide), Assembly.sourcesBound_reads _ _ _ _ (by decide)⟩)).seq
      (Assembly.code_namesAccounted _ 5 (Construction.prefix_sources _ _ _))
private theorem continuation_names : NamesAccounted continuation.code 5 := by
  rw [continuation_code]
  have initial : NamesAccounted initialRaw 5 := by simpa only [initial_code] using initial_names
  exact (selectSlice_names 3 3 5).seq (Dispatch.names
    ((((selectSlice_names 1 1 5).seq (Assembly.code_namesAccounted _ 5 (Construction.prefix_sources _ _ _))).seq
      (Assembly.code_namesAccounted _ 5 (Construction.prefix_sources _ _ _))).seq initial)
    (Assembly.code_namesAccounted _ 5 (Construction.prefix_sources _ _ _)) 2 1)
private def callerTime := BLSCaller.timeBudget (base := base) (key := .nat) (val := .atom ()) layout
  requestRep.encoding.words (CallerStep.width callerLayout) 26 (fun _ => 8) 1000 1000 2
private def callerWords := BLSCaller.codeBudget (base := base) (key := .nat) (val := .atom ()) layout
  requestRep.encoding.words (CallerStep.width callerLayout) 200 (fun _ => 100) 5000 5000 2
private theorem caller_time : Interactive.TimeBoundOn admitted port .unit callerInput (caller 2) callerTime :=
  BLSCaller.time (base := base) (key := .nat) (val := .atom ()) layout default 3 (by decide)
    primitives comparison comparison_correct (fun _ => response) (fun _ => response_buffers) (by decide) draw drawSource
    draw_correct draw_law localDomain advance advance_valid requestRep layout.point.representation (by decide)
    continuation (by decide) requestRep initial initialCode (by decide) (by decide)
    draw_time (fun _ => response_bound) continuation_time initial_time 2 admitted initial_valid (fun _ valid => valid)
private theorem caller_words : ((caller 2).lower port).descriptionWords ≤ callerWords :=
  BLSCaller.words (base := base) (key := .nat) (val := .atom ()) layout default 3 (by decide)
    primitives comparison comparison_correct (fun _ => response) (fun _ => response_buffers) (by decide) draw advance
    requestRep layout.point.representation (by decide) continuation (by decide) requestRep initial initialCode (by decide) (by decide)
    draw_words (fun _ => response_bound) continuation_words initial_words 2
private theorem caller_memory (tape : RandomTape 10) (value) (valid : admitted value)
    (before : State 10) (holds : callerInput.Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result 10) (reached : some finished ∈ support ((caller 2).execute port .unit tape before)) :
    ∃ execution : WordIO.Exec .unit tape ((caller 2).lower port) before finished.state finished.trace finished.time finished.net finished.peak,
      ∀ between, execution.Visits between →
        (((caller 2).lower port).staticWords registers buffers : Int) + between.liveMem (max buffers ((caller 2).lower port).memBound) ≤
          callerWords + 4 * (5 + callerWords) + registers + 3 * buffers + before.liveMem buffers + callerTime := by
  have certified := BLSCaller.resources (base := base) (key := .nat) (val := .atom ())
    (drawSlots := 3) (responseSlots := 3) (callerSlots := 5) layout default 3 (by decide)
    primitives comparison comparison_correct (fun _ => response) (fun _ => response_buffers) (by decide) draw drawSource
    draw_correct draw_law localDomain advance advance_valid requestRep layout.point.representation (by decide)
    continuation (by decide) requestRep initial initialCode (by decide) (by decide)
    draw_time draw_words (fun _ => response_bound) continuation_time initial_time continuation_words initial_words
    2 admitted initial_valid (fun _ valid => valid) (by decide) draw_names (fun _ => response_names)
    (by decide) (by decide) continuation_names initial_names tape value valid before holds registers buffers initialRegisters initialBuffers finished reached
  obtain ⟨_, _, _, _, execution, bounded⟩ := certified
  exact ⟨execution, fun between visited => (bounded between visited).2.2.2⟩
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

private def executeCaller (fuel : Nat) (value : BLSCallerPackets.Request layout 3 × layout.store.Value) (replies : List (Word 10)) :=
  let initial := callerInput.initial value
  let before := { initial with bufs := fun b => if b = 200 then #[91] else initial.bufs b
                               caps := fun b => if b = 200 then 4 else initial.caps b
                               regs := fun r => if r = 200 then 99 else initial.regs r
                               tapePos := 9 }
  (WordIO.run .unit RandomTape.zero 200000 ((caller fuel).lower port) before replies).map
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
  let emptyStore : Array (Word 10) := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  unless executeCaller 0 (.inl 3, empty) [3, 2, 3, 1, 55] ==
      some (#[1, 0, 3, 0, 0, 3, 0] ++ emptyStore, [], [3, 2, 3, 1, 55], #[91], 4, 99, 9) do
    throwError "zero-fuel BLS caller failed to retain the pending request and private store"
  unless executeCaller 1 (.inl 3, empty) [3, 2, 3, 1, 55] ==
      some (#[1, 1, 0, 2, 1, 0, 2] ++ emptyStore,
        [.output 3, .invoke, .input 3, .input 2], [3, 1, 55], #[91], 4, 99, 9) do
    throwError "BLS caller cutoff failed to retain the adaptively selected hash request"
  unless executeCaller 2 (.inl 3, empty) [3, 2, 3, 1, 55] ==
      some (#[0, 1, 0, 0, 0, 0, 0, 1, 2, 1, 0, 0, 1, 2, 1, 0, 0, 0, 0, 0, 0, 0],
        [.output 3, .invoke, .input 3, .input 2, .output 3, .invoke, .input 3, .input 1], [55], #[91], 4, 99, 9) do
    throwError "adaptive BLS caller failed random selection, lazy hashing or final state preservation"
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``SumContext.merge, ``SumContext.merge_time, ``SumContext.merge_words, ``SumContext.merge_names,
      ``BLSCallerPackets.prepare, ``BLSCallerPackets.finish, ``BLSCallerPackets.request_bytes,
      ``BLSCallerPackets.prepare_time, ``BLSCallerPackets.prepare_words, ``BLSCallerPackets.prepare_names,
      ``BLSCallerPackets.finish_time, ``BLSCallerPackets.finish_words, ``BLSCallerPackets.finish_names, ``prepared_bytes,
      ``Synchronizes.of_map_eq, ``Synchronizes.iff_map_eq, ``BLSCallerHandler.refines, ``BLSCallerHandler.time,
      ``BLSCallerHandler.words, ``BLSCallerHandler.names, ``BLSCallerHandler.descriptionFits,
      ``BLSCallerHandler.denote_source, ``BLSCallerHandler.synchronizes, ``BLSCallerHandler.ready_of_reserved,
      ``BLSCallerHandler.reserved_after, ``draw_correct, ``draw_law, ``handler_refines, ``handler_source, ``handler_preserves,
      ``Synchronizes.symm, ``Synchronizes.left_support, ``BLSCaller.preserves, ``BLSCaller.initial_invariant,
      ``BLSCaller.refines, ``BLSCaller.observe_source, ``BLSCaller.time, ``BLSCaller.words, ``BLSCaller.names,
      ``BLSCaller.descriptionFits, ``BLSCaller.resources, ``caller_implements, ``advance_matches, ``initial_matches,
      ``CallerControl.start_store, ``BLSCallerHandler.growth, ``BLSCaller.start_postcondition,
      ``BLSCaller.Postcondition.extraction_room, ``BLSCaller.execution_postcondition,
      ``caller_postcondition, ``extraction_reserved, ``caller_extraction_room,
      ``empty_admitted, ``caller_refines, ``caller_source, ``caller_time, ``caller_words, ``caller_memory] do
    let axioms ← collectAxioms name
    for dependency in axioms do
      unless dependency ∈ allowed do throwError "unexpected axiom {dependency} in {name}"

end SignaturesTest.CaliperBLSPackets
