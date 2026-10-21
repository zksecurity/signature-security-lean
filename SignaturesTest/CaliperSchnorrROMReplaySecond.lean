import Signatures.Runtime.Caliper.SchnorrROMPassPresentation
import Signatures.Runtime.Caliper.SchnorrROMReplaySecondSource
import Lean

open Caliper OracleComp OracleSpec Signatures.Runtime Signatures.Runtime.CaliperBackend BoundedSource
namespace SignaturesTest.CaliperSchnorrROMReplaySecond
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
private abbrev Store := Schnorr.ListROM.Shared.Store (ZMod 7) (Word 16) Nat
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
example (done : Bool) (q : CallerPackets.Request config) (fuel : Nat) :
    ((ReplaySecond.program config (caller done q) operations fuel).lower (Fresh.port config.handler.sampler.tape)).DescriptionFits :=
  ReplaySecond.descriptionFits config (caller done q) operations (nameRoom done q) fuel
private def run (done : Bool) (q : CallerPackets.Request config) (fuel : Nat) (generator publicKey : Word 16)
    (slot : Fin 65536) (replacement : ZMod 7)
    (saved remaining : List (Schnorr.TapeCell (ZMod 7))) (replies : List (Word 16)) := do
  let original : Store := (((generator, publicKey), [((2, publicKey), 6)], [((2, publicKey), 3)]), saved, remaining)
  let old : config.handler.store.Value ← if valid : config.handler.store.valid original then some ⟨original, valid⟩ else none
  let first : Terminal.Output config := (.inr (forge ⟨publicKey, trivial⟩, ⟨3, trivial⟩), old)
  let request : ReplaySecond.Request config := ((⟨slot.val, slot.isLt⟩, ⟨replacement, trivial⟩), first)
  let value : {value : ReplaySecond.Request config // ReplaySecond.ready config fuel value} ←
    if valid : ReplaySecond.ready config fuel request then some ⟨request, valid⟩ else none
  let initial := (ReplaySecond.input config fuel).initial value
  let before := { initial with
    bufs := fun i => if i = 200 then #[77] else initial.bufs i
    caps := fun i => if i = 200 then 4 else initial.caps i
    regs := fun i => if i = 99 then 91 else initial.regs i
    tapePos := 9 }
  let result ← WordIO.run .unit RandomTape.zero 1000000
    ((ReplaySecond.program config (caller done q) operations fuel).lower (Fresh.port config.handler.sampler.tape)) before replies
  pure (((ReplaySecond.output config).encoding.decode (result.state.bufs 0).toList).map
      (fun answer : Terminal.Output config × ReplaySecond.Request config =>
        (Terminal.observed config answer.1,
          (ReplaySecond.rawInput config).encoding.encode answer.2 == (ReplaySecond.rawInput config).encoding.encode value.val)),
    result.trace, result.remaining, result.state.bufs 200, result.state.caps 200, result.state.regs 99,
    result.state.tapePos, (List.range 30).all (fun i => result.state.caps (i + 1) == 0),
    decide (result.time ≤ ReplaySecond.timeBudget config (caller done q) operations budget (localBudget done q) fuel))
private def store (g pk : Word 16) (managed live : Signing.Table Nat (ZMod 7) (Word 16))
    (saved remaining : List (Schnorr.TapeCell (ZMod 7))) : Store := (((g, pk), managed, live), saved, remaining)

private def groupConfig : Signing.Enumerated.Configuration 16 Nat (ZMod 7) (ZMod 7) where
  sampler := params
  message := config.message
  point := PrivateSampler.Enumerated.scalar params
  capacityPred := 2
  countFits := by decide
  storageFits := by decide
private theorem original_sampler {A : Type} (caller : Pass.Caller groupConfig A) (ops : Handler.Operations groupConfig)
    (fuel : Nat) (witness : Pass.Caller.Source groupConfig caller fuel)
    (value : {value : ReplaySecond.Request groupConfig // ReplaySecond.ready groupConfig fuel value}) :
    ReplaySecond.observed groupConfig <$> ReplaySecond.source groupConfig caller ops fuel value =
      (fun result => ((some result.1, result.2), value.val)) <$>
        Schnorr.ListROM.Shared.tapeRun
          ((Schnorr.ListROM.pass (G₂ := ZMod 7) (K := Nat)
            (Subtype.val <$> witness.program
              (witness.inputView (Pass.Initialization.start groupConfig (ReplaySecond.nextInput groupConfig fuel value)).1))).run
                (value.val.2.2.val.1.1, [], []))
          (ReplayRestart.tapes (Schnorr.RawTape.restart value.val.1.1.val value.val.1.2.val
            ⟨value.val.2.2.val.2.1, value.val.2.2.val.2.2⟩)) := by
  have same : PrivateSampler.Enumerated.sampleable groupConfig.sampler = FinEnum.SampleableType (ZMod 7) :=
    PrivateSampler.Enumerated.sampleable_finEnum 10 (by decide) (by decide) (by decide)
  have original := ReplaySecond.source_original (G₂ := ZMod 7) (K := Nat) groupConfig caller ops fuel witness value
  rw [same] at original
  exact original

open Lean in
run_cmd do
  let old : List (Schnorr.TapeCell (ZMod 7)) := [(3, 0, 1), (1, 3, 0), (9, 0, 10)]
  let reset : List (Schnorr.TapeCell (ZMod 7)) := [(3, 0, 1), (9, 0, 10), (1, 4, 0)]
  unless run true random 0 3 5 0 4 old [(1, 6, 0)] [88] ==
      some (some ((some ((2, 5, 0), 4), store 3 5 [] [((2, 5), 4)] reset [(3, 0, 1), (9, 0, 10)]), true),
        [], [88], #[77], 4, 91, 9, true, true) do
    throwError "restart/second pass lost the first result, retained old caches or reused the old remaining tape"
  unless run false random 1 3 5 0 4 old [] [88] ==
      some (some ((some ((2, 5, 0), 4), store 3 5 [] [((2, 5), 4)] reset [(3, 0, 1)]), true),
        [], [88], #[77], 4, 91, 9, true, true) do
    throwError "second pass failed private replay followed by replacement-challenge hashing"
  unless run false random 0 3 5 0 4 old [] [88] ==
      some (some ((none, store 3 5 [] [] reset reset), true), [], [88], #[77], 4, 91, 9, true, true) do
    throwError "cutoff must preserve both restarted tapes and the complete first result"
  let short : List (Schnorr.TapeCell (ZMod 7)) := [(3, 0, 1), (1, 3, 0)]
  unless run false random 1 3 5 0 4 short [] [7, 4, 88] ==
      some (some ((some ((2, 5, 0), 4), store 3 5 [] [((2, 5), 4)] [(3, 0, 1), (1, 4, 0), (9, 0, 4)] [(3, 0, 1)]), true),
        [.output 7, .invoke, .input 7, .input 4], [88], #[77], 4, 91, 9, true, true) do
    throwError "second pass failed fresh private sampling or dropped its retained prefix"
  unless run false hashed 1 3 5 0 4 old [] [88] ==
      some (some ((some ((2, 5, 0), 4), store 3 5 [((2, 5), 4)] [((2, 5), 4)] reset [(3, 0, 1), (9, 0, 10)]), true),
        [], [88], #[77], 4, 91, 9, true, true) do
    throwError "second pass must rebuild managed/LIVE caches and reuse its own final hash"
  unless run true random 0 9 11 0 0 [] [] [88] ==
      some (some ((some ((2, 11, 0), 0), store 9 11 [] [((2, 11), 0)] [(1, 0, 0)] []), true),
        [], [88], #[77], 4, 91, 9, true, true) do
    throwError "restart lost a zero challenge or the runtime public points"
  for slot in [(1 : Fin 65536), 65535] do
    unless run true random 0 3 5 slot 4 old [] [88] ==
        some (some ((some ((2, 5, 0), 3), store 3 5 [] [((2, 5), 3)] (old ++ [(1, 4, 0)]) [(3, 0, 1), (9, 0, 10), (1, 4, 0)]), true),
          [], [88], #[77], 4, 91, 9, true, true) do
      throwError "restart must retain earlier public challenges in chronological order"
  let full : List (Schnorr.TapeCell (ZMod 7)) := List.replicate 8 (3, 0, 1)
  unless run true random 0 3 5 0 4 full [] [] ==
      some (some ((some ((2, 5, 0), 4), store 3 5 [] [((2, 5), 4)] (full ++ [(1, 4, 0)]) full), true),
        [], [], #[77], 4, 91, 9, true, true) do
    throwError "second pass rejected the exact admitted tape boundary"
  unless run true random 0 3 5 0 4 (List.replicate 9 (3, 0, 1)) [] [] == none &&
      run false random 3 3 5 0 4 [] [] [] == none &&
      run false random 1 3 5 0 4 short [] [7] == none do
    throwError "second pass accepted insufficient tape/cache reserve or an incomplete reply"
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``Pass.buffers, ``Pass.savedNameFits, ``ReplaySecond.prepare_bytes, ``ReplaySecond.repack_bytes,
      ``ReplaySecond.next_ready, ``ReplaySecond.initialization_time, ``ReplaySecond.initialization_words,
      ``ReplaySecond.initialization_buffers, ``ReplaySecond.initialization_names,
      ``ReplaySecond.pass_refines, ``ReplaySecond.refines, ``ReplaySecond.retained_first, ``ReplaySecond.ready_after_first,
      ``ReplaySecond.buffers, ``ReplaySecond.descriptionFits, ``ReplaySecond.time, ``ReplaySecond.words,
      ``ReplaySecond.names, ``ReplaySecond.resources, ``ReplaySecond.source_original, ``ReplaySecond.observe_original,
      ``original_sampler] do
    for dependency in (← collectAxioms name) do
      unless dependency ∈ allowed do throwError "unexpected axiom {dependency} in {name}"

end SignaturesTest.CaliperSchnorrROMReplaySecond
