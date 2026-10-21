import Signatures.Runtime.Caliper.SchnorrROMPassPresentation
import Signatures.Runtime.Caliper.SchnorrROMReplayForkSource
import Lean

open Caliper OracleComp OracleSpec Signatures.Runtime Signatures.Runtime.CaliperBackend BoundedSource
namespace SignaturesTest.CaliperSchnorrROMReplayFork
open SchnorrROMTape SchnorrROM

private instance : Fact (Nat.Prime 7) := ⟨by decide⟩
private instance : SMul (ZMod 7) (Word 16) := ⟨fun scalar point => BitVec.ofNat 16 scalar.val * point⟩
private def params : PrivateSampler.Enumerated.Parameters 16 (ZMod 7) :=
  PrivateSampler.Enumerated.Parameters.ofFinEnum 16 (ZMod 7) 10 (by decide) (by decide) (by decide)
private def config : Signing.Enumerated.Configuration 16 Nat (ZMod 7) (Word 16) where
  sampler := params
  message := Layout.counter 16 256 (by decide) (by decide)
  point := Layout.all (wordRepresentation 16 (by decide))
  capacityPred := 2
  countFits := by decide
  storageFits := by decide
private def scale : Implementation .unit config.handler.core.arithmetic.scaleArgs config.handler.core.point (fun value => value.1 • value.2) where
  preserves _ _ := trivial
  program := ((WordBinary.realizer .unit .mul (by decide)).viewInput config.handler.core.arithmetic.scaleArgs.representation
    (fun value => (BitVec.ofNat 16 value.val.1.val, value.val.2)) (fun _ => rfl)).viewOutput config.handler.core.point.representation
      (fun value => ⟨value.val.1 • value.val.2, trivial⟩) (fun _ => rfl)
private def sub : Implementation .unit config.handler.core.arithmetic.points config.handler.core.point (fun value => value.1 - value.2) where
  preserves _ _ := trivial
  program := ((WordBinary.realizer .unit .sub (by decide)).viewInput config.handler.core.arithmetic.points.representation
    (fun value => value.val) (fun _ => rfl)).viewOutput config.handler.core.point.representation
      (fun value => ⟨value.val.1 - value.val.2, trivial⟩) (fun _ => rfl)
private def operations : Handler.Operations config where
  scale := scale
  sub := sub
  slots := 3
  scaleNames := ⟨by decide, by decide⟩
  subNames := ⟨by decide, by decide⟩
  reserve := by decide
private def budget : Handler.Budget config operations where
  scaleTime := 6
  scaleWords := 27
  subTime := 6
  subWords := 27
  scale := ⟨fun _ => by change 6 ≤ 6; omega, by decide⟩
  sub := ⟨fun _ => by change 6 ≤ 6; omega, by decide⟩

private abbrev Key := config.point.Value
private def layout := Pass.control config config.point.representation (by decide)
private def forge (key : Key) : (ForgeryHash.forgery config).Value :=
  ⟨(2, key.val, 0), by change 2 < 256; decide, key.property, trivial⟩
private def next (done : Bool) (q : CallerPackets.Request config) (key : Key) :=
  if done then Sum.inl (forge key) else Sum.inr (q, key)
private def parts (done : Bool) (q : CallerPackets.Request config) : List (ByteRoute.Part 16) :=
  if done then [.literal [0, 2], .slice 0 1, .literal [0, 0, 0]]
  else [.literal (1 :: (CallerPackets.request config).encoding.encode q), .slice 0 1]
private theorem parts_size (done : Bool) (q : CallerPackets.Request config) :
    ByteRoute.words (parts done q) = (CallerStep.next layout).encoding.words := by
  cases done <;> simp only [parts, Bool.false_eq_true, ↓reduceIte, ByteRoute.words, List.length_cons, List.length_nil, Encoding.encode_length] <;> rfl
private def initialCode (done : Bool) (q : CallerPackets.Request config) :
    Realizer .unit config.point.representation (CallerStep.next layout) (next done q) :=
  ByteRoute.realizer _ _ _ (parts done q) (by decide)
    (by cases done <;> exact ⟨by decide, trivial⟩) (parts_size done q)
    (by intro key; cases done <;> rcases q with (q | q) | q <;> rfl)
private def advanceCode (q : CallerPackets.Request config) :
    Realizer .unit (CallerStep.resume layout) (CallerStep.next layout)
      (fun value => next true q value.1) :=
  ByteRoute.realizer _ _ _ (parts true q) (by decide) (by exact ⟨by decide, trivial⟩) (parts_size true q)
    (by intro value; rcases value with ⟨key, (answer | answer) | answer⟩ <;> rfl)
private theorem initialize_buffers (done : Bool) (q : CallerPackets.Request config) : (initialCode done q).code.memBound ≤ 2 :=
  ByteRoute.buffers _ _ _ _ _ _ _ _
private theorem continue_buffers (q : CallerPackets.Request config) : (advanceCode q).code.memBound ≤ 2 :=
  ByteRoute.buffers _ _ _ _ _ _ _ _
private def caller (done : Bool) (q : CallerPackets.Request config) : Pass.Caller config Key where
  state := config.point.representation
  fits := by decide
  advance := fun value => next true q value.1
  continuation := advanceCode q
  localNameFits := by have := continue_buffers q; change max 2 (advanceCode q).code.memBound < 65536; omega
  initial := next done q
  initialization := initialCode done q
  initialNameFits := by have := initialize_buffers done q; change max 2 (initialCode done q).code.memBound < 65536; omega
private def localBudget (done : Bool) (q : CallerPackets.Request config) : Caller.LocalBudget config ((caller done q).routines config) where
  localTime := 48
  initialTime := 48
  localWords := 170
  initialWords := 170
  local_time := by
    change ∀ value, (advanceCode q).time value ≤ 48
    exact ByteRoute.time _ _ _ _ _ _ _ _
  initial_time := by
    change ∀ value, (initialCode done q).time value ≤ 48
    exact ByteRoute.time _ _ _ _ _ _ _ _
  local_words := by
    change descriptionWords (advanceCode q).code ≤ 170
    exact ByteRoute.codeWords _ _ _ _ _ _ _ _
  initial_words := by
    change descriptionWords (initialCode done q).code ≤ 170
    exact ByteRoute.codeWords _ _ _ _ _ _ _ _

private def random : CallerPackets.Request config := .inl (.inl ⟨7, by change 7 < 65534; decide⟩)
private def hashed : CallerPackets.Request config := .inl (.inr ⟨(2, 5), by change 2 < 256; decide, trivial⟩)
private def signed : CallerPackets.Request config := .inr ⟨2, by change 2 < 256; decide⟩
private instance (value : Schnorr.ListROM.Shared.Tape (ZMod 7)) : Decidable ((Pass.Initialization.tapes config).valid value) := by
  change Decidable ((value.1.length ≤ 10 ∧ ∀ cell ∈ value.1, cell.1 < 65536 ∧ True ∧ cell.2.2 < 65536) ∧
    (value.2.length ≤ 10 ∧ ∀ cell ∈ value.2, cell.1 < 65536 ∧ True ∧ cell.2.2 < 65536))
  infer_instance
private abbrev Store := Schnorr.ListROM.Shared.Store (ZMod 7) (Word 16) Nat
private abbrev Observation := Option ((Nat × Word 16 × ZMod 7) × ZMod 7) × Store
private instance : BEq Observation := inferInstance
private instance (value : Store) : Decidable (config.handler.store.valid value) := by
  change Decidable ((((True ∧ True) ∧
    (value.1.2.1.length ≤ 3 ∧ ∀ entry ∈ value.1.2.1, (entry.1.1 < 256 ∧ True) ∧ True) ∧
    (value.1.2.2.length ≤ 3 ∧ ∀ entry ∈ value.1.2.2, (entry.1.1 < 256 ∧ True) ∧ True)) ∧
    (value.2.1.length ≤ 10 ∧ ∀ cell ∈ value.2.1, cell.1 < 65536 ∧ True ∧ cell.2.2 < 65536) ∧
    (value.2.2.length ≤ 10 ∧ ∀ cell ∈ value.2.2, cell.1 < 65536 ∧ True ∧ cell.2.2 < 65536)))
  infer_instance

private theorem nameRoom (done : Bool) (q : CallerPackets.Request config) : Pass.replayNameRoom config (caller done q) operations := by
  have initial := initialize_buffers done q
  have localCode := continue_buffers q
  change 7 < 65536 ∧ (advanceCode q).code.memBound + 1 < 65536 ∧ (initialCode done q).code.memBound + 1 < 65536
  omega
example (qH : Fin 65535) (done : Bool) (q : CallerPackets.Request config) (fuel : Nat) :
    ((ReplayFork.program config (caller done q) operations qH.val (by have := qH.isLt; omega) fuel).lower (Fresh.port config.handler.sampler.tape)).DescriptionFits :=
  ReplayFork.descriptionFits config (caller done q) operations qH.val (by have := qH.isLt; omega) (nameRoom done q) fuel

private def run (qH : Fin 65535) (done : Bool) (q : CallerPackets.Request config) (fuel : Nat) (g pk : Word 16)
    (saved remaining : List (Schnorr.TapeCell (ZMod 7))) (replies : List (Word 16)) := do
  let tapes : (Pass.Initialization.tapes config).Value ← if valid : (Pass.Initialization.tapes config).valid (saved, remaining) then
    some ⟨(saved, remaining), valid⟩ else none
  let raw : Pass.Initialization.Input config := (tapes, ⟨(g, pk), trivial, trivial⟩)
  let value : {value : Pass.Initialization.Input config // Pass.Replay.ready config fuel value} ←
    if valid : Pass.Replay.ready config fuel raw then some ⟨raw, valid⟩ else none
  let initial := (ReplayFirst.input config fuel).initial value
  let before := { initial with bufs := fun i => if i = 200 then #[77] else initial.bufs i
                               caps := fun i => if i = 200 then 4 else initial.caps i
                               regs := fun i => if i = 99 then 91 else initial.regs i
                               tapePos := 9 }
  let body := ReplayFork.program config (caller done q) operations qH.val (by have := qH.isLt; omega) fuel
  let result ← WordIO.run .unit RandomTape.zero 1000000 (body.lower (Fresh.port config.handler.sampler.tape)) before replies
  pure (((ReplayFork.output config).encoding.decode (result.state.bufs 0).toList).map
      (fun answer : ReplayFork.Result config => Sum.elim (fun _ => none)
        (fun pair : Terminal.Output config × Terminal.Output config => some (Terminal.observed config pair.1, Terminal.observed config pair.2)) answer),
    result.trace, result.remaining, result.state.bufs 200, result.state.caps 200, result.state.regs 99,
    result.state.tapePos, (List.range 30).all (fun i => result.state.caps (i + 1) == 0),
    decide (result.time ≤ ReplayFork.timeBudget config (caller done q) operations qH.val (by have := qH.isLt; omega) budget (localBudget done q) fuel))

private def store (g pk : Word 16) (managed live : Signing.Table Nat (ZMod 7) (Word 16))
    (saved remaining : List (Schnorr.TapeCell (ZMod 7))) : Store := (((g, pk), managed, live), saved, remaining)
private def runFinish (accepted : Bool) := do
  let first : Terminal.Output config := (.inl (),
    ⟨store 3 5 [((31, 7), 1)] [((21, 8), 2)] [(3, 0, 4)] [(1, 5, 0)], by decide⟩)
  let forge : (ForgeryHash.forgery config).Value := ⟨(2, 9, 6), by change 2 < 256; decide, trivial, trivial⟩
  let second : Terminal.Output config := (.inr (forge, ⟨4, trivial⟩),
    ⟨store 11 13 [] [((2, 9), 4)] [(1, 4, 0)] [], by decide⟩)
  let frame : ReplayMatch.Frame config := (second, ((⟨65535, by change 65535 < 65536; decide⟩, ⟨6, trivial⟩), first))
  let value : (Selection.boolean config).Value × ReplayMatch.Frame config := (⟨accepted, trivial⟩, frame)
  let initial := (ReplayMatch.output config).initial value
  let before := { initial with bufs := fun i => if i = 200 then #[77] else initial.bufs i
                               caps := fun i => if i = 200 then 4 else initial.caps i
                               regs := fun i => if i = 99 then 91 else initial.regs i
                               tapePos := 9 }
  let result ← Caliper.run .unit RandomTape.zero 100000 (ReplayFork.finish config).code before
  let expected : ReplayFork.Result config := if accepted then .inr (first, second) else .inl ()
  pure ((result.1.bufs 0).toList == (ReplayFork.output config).encoding.encode expected,
    result.1.bufs 200, result.1.caps 200, result.1.regs 99, result.1.tapePos,
    (List.range 30).all (fun i => result.1.caps (i + 1) == 0), decide (result.2.1 ≤ ReplayFork.finishTime config))

open Lean in
run_cmd do
  let old : List (Schnorr.TapeCell (ZMod 7)) := [(3, 0, 9), (1, 4, 0)]
  let reset : List (Schnorr.TapeCell (ZMod 7)) := [(3, 0, 9), (1, 5, 0)]
  let privateTail : List (Schnorr.TapeCell (ZMod 7)) := [(3, 0, 9)]
  unless run 0 false random 0 3 0 old old [6, 5, 88] ==
      some (some none, [], [6, 5, 88], #[77], 4, 91, 9, true, true) do
    throwError "fork cutoff must skip fresh sampling and replay"
  unless run 0 true random 0 3 5 old old [6, 5, 88] ==
      some (some none, [], [6, 5, 88], #[77], 4, 91, 9, true, true) do
    throwError "invalid first signature must skip the fresh draw"
  unless run 0 true random 0 3 0 old old [6, 4, 6, 6, 88] ==
      some (some none, [.output 6, .invoke, .input 6, .input 4], [6, 6, 88], #[77], 4, 91, 9, true, true) do
    throwError "duplicate challenge must skip the second pass"
  for qH in [(0 : Fin 65535), 65534] do
    unless run qH true random 0 3 0 old old [6, 5, 6, 6, 88] ==
        some (some (some ((some ((2, 0, 0), 4), store 3 0 [] [((2, 0), 4)] old privateTail),
          (some ((2, 0, 0), 5), store 3 0 [] [((2, 0), 5)] reset privateTail))),
          [.output 6, .invoke, .input 6, .input 5], [6, 6, 88], #[77], 4, 91, 9, true, true) do
      throwError "successful fork lost ordered pass results, tapes, trace or its resource bound"
  let two : List (Schnorr.TapeCell (ZMod 7)) := [(1, 3, 0), (1, 4, 0)]
  let twoReset : List (Schnorr.TapeCell (ZMod 7)) := [(1, 3, 0), (1, 5, 0)]
  unless run 1 false hashed 1 3 0 two two [6, 5, 88] ==
      some (some (some ((some ((2, 0, 0), 4), store 3 0 [((2, 5), 3)] [((2, 0), 4), ((2, 5), 3)] two []),
        (some ((2, 0, 0), 5), store 3 0 [((2, 5), 3)] [((2, 0), 5), ((2, 5), 3)] twoReset []))),
        [.output 6, .invoke, .input 6, .input 5], [88], #[77], 4, 91, 9, true, true) do
    throwError "fork failed at a nonzero selected public ordinal"
  unless run 0 false hashed 1 3 0 two two [6, 5, 88] ==
      some (some none, [], [6, 5, 88], #[77], 4, 91, 9, true, true) do
    throwError "out-of-allowance selection must skip both later phases"
  unless run 0 true random 0 3 0 [] [] [6, 4, 6, 5, 88] ==
      some (some (some ((some ((2, 0, 0), 4), store 3 0 [] [((2, 0), 4)] [(1, 4, 0)] []),
        (some ((2, 0, 0), 5), store 3 0 [] [((2, 0), 5)] [(1, 5, 0)] []))),
        [.output 6, .invoke, .input 6, .input 4, .output 6, .invoke, .input 6, .input 5], [88], #[77], 4, 91, 9, true, true) do
    throwError "fork from empty tapes failed fresh first hashing or draw order"
  unless run 0 true random 0 3 0 old old [6] == none && run 0 true random 2 3 0 [] [] [] == none do
    throwError "fork admitted incomplete replies or insufficient replay reservation"
  for accepted in [false, true] do
    unless runFinish accepted == some (true, #[77], 4, 91, 9, true, true) do
      throwError "second selection exit lost canonical failure padding, union bytes or result order"
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``ReplayFork.accept_bytes, ``ReplayFork.chooseMatch_bytes, ``ReplayFork.finish,
      ``ReplayFork.finish_time, ``ReplayFork.finish_words, ``ReplayFork.finish_names, ``ReplayFork.finish_buffers,
      ``ReplayFork.chooseGuard_bytes, ``ReplayFork.guardChoice_ready, ``ReplayFork.second_refines,
      ``ReplayFork.after_refines, ``ReplayFork.first_ready, ``ReplayFork.refines,
      ``ReplayFork.time, ``ReplayFork.words, ``ReplayFork.names, ``ReplayFork.buffers,
      ``ReplayFork.descriptionFits, ``ReplayFork.resources, ``ReplayFork.guarded_range,
      ``ReplayFork.indexed_flag, ``ReplayFork.selection_range, ``ReplayFork.pass_range,
      ``ReplayFork.first_gate_original, ``ReplayFork.second_exit_original] do
    for dependency in (← collectAxioms name) do
      unless dependency ∈ allowed do throwError "unexpected axiom {dependency} in {name}"

end SignaturesTest.CaliperSchnorrROMReplayFork
