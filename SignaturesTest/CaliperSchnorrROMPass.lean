import Signatures.Runtime.Caliper.SchnorrROMPassPresentation
import Signatures.Runtime.Caliper.SchnorrROMPassGrowth
import Lean

open Caliper OracleComp OracleSpec Signatures.Runtime Signatures.Runtime.CaliperBackend BoundedSource
namespace SignaturesTest.CaliperSchnorrROMPass
open SchnorrROMTape SchnorrROM

private instance : Fact (Nat.Prime 7) := ⟨by decide⟩
private instance : SMul (ZMod 7) (Word 16) := ⟨fun scalar point => BitVec.ofNat 16 scalar.val * point⟩
private def params : PrivateSampler.Enumerated.Parameters 16 (ZMod 7) :=
  PrivateSampler.Enumerated.Parameters.ofFinEnum 16 (ZMod 7) 12 (by decide) (by decide) (by decide)
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
private theorem scaleBound : scale.BoundedBy 6 27 := ⟨fun _ => by change 6 ≤ 6; omega, by decide⟩
private theorem subBound : sub.BoundedBy 6 27 := ⟨fun _ => by change 6 ≤ 6; omega, by decide⟩
private def operations : Handler.Operations config where
  scale := scale
  sub := sub
  slots := 3
  scaleNames := ⟨by decide, by decide⟩
  subNames := ⟨by decide, by decide⟩
  reserve := by decide
  signing := Handler.fullField config scale sub ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (by decide) scaleBound subBound
private def budget : Handler.Budget config operations where
  scaleTime := 6
  scaleWords := 27
  subTime := 6
  subWords := 27
  scale := scaleBound
  sub := subBound

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

private theorem terminating (done : Bool) (q : CallerPackets.Request config) : (caller done q).Terminates config 1 := by
  intro input
  cases done
  · intro answer
    trivial
  · trivial
private noncomputable def sourceWitness (done : Bool) (q : CallerPackets.Request config) : Pass.Caller.Source config (caller done q) 1 :=
  Pass.Caller.Source.ofCaller config (caller done q) 1 (terminating done q)
example (done : Bool) (q : CallerPackets.Request config) (key : Key) :
    (sourceWitness done q).machine.unroll 1 ((caller done q).initial key) = some <$> (sourceWitness done q).program key :=
  Pass.Caller.Source.ofCaller_run config (caller done q) 1 (terminating done q) key

private def random : CallerPackets.Request config := .inl (.inl ⟨7, by change 7 < 65534; decide⟩)
private def hashed : CallerPackets.Request config := .inl (.inr ⟨(2, 5), by change 2 < 256; decide, trivial⟩)
private def signed : CallerPackets.Request config := .inr ⟨2, by change 2 < 256; decide⟩
private instance (value : Schnorr.ListROM.Shared.Tape (ZMod 7)) : Decidable ((Pass.Initialization.tapes config).valid value) := by
  change Decidable ((value.1.length ≤ 12 ∧ ∀ cell ∈ value.1, cell.1 < 65536 ∧ True ∧ cell.2.2 < 65536) ∧
    (value.2.length ≤ 12 ∧ ∀ cell ∈ value.2, cell.1 < 65536 ∧ True ∧ cell.2.2 < 65536))
  infer_instance
private instance (fuel : Nat) (value : Pass.Initialization.Input config) : Decidable (Pass.Initialization.admitted config fuel value) := by
  unfold Pass.Initialization.admitted
  infer_instance
private def run (done : Bool) (q : CallerPackets.Request config) (fuel : Nat) (generator publicKey : Word 16)
    (saved remaining : List (Schnorr.TapeCell (ZMod 7))) (replies : List (Word 16)) := do
  let tapes : (Pass.Initialization.tapes config).Value ← if valid : (Pass.Initialization.tapes config).valid (saved, remaining) then
    some ⟨(saved, remaining), valid⟩ else none
  let value : Pass.Initialization.Input config := (tapes, ⟨(generator, publicKey), trivial, trivial⟩)
  if !decide (Pass.Initialization.admitted config fuel value) then none else do
    let initial := (Pass.Initialization.input config).initial value
    let before := { initial with
      bufs := fun i => if i = 200 then #[77] else initial.bufs i
      caps := fun i => if i = 200 then 4 else initial.caps i
      regs := fun i => if i = 99 then 91 else initial.regs i
      tapePos := 9 }
    let result ← WordIO.run .unit RandomTape.zero 1000000
      ((Pass.program config (caller done q) operations fuel).lower (Fresh.port config.handler.sampler.tape)) before replies
    pure (((Pass.output config (caller done q)).encoding.decode (result.state.bufs 0).toList).map (Terminal.observed config),
      result.trace, result.remaining, result.state.bufs 200, result.state.caps 200, result.state.regs 99,
      result.state.tapePos, (List.range 30).all (fun i => result.state.caps (i + 1) == 0),
      decide (result.time ≤ Pass.timeBudget config (caller done q) operations budget (localBudget done q) fuel))
private def store (g pk : Word 16) (managed live : Signing.Table Nat (ZMod 7) (Word 16))
    (saved remaining : List (Schnorr.TapeCell (ZMod 7))) : Schnorr.ListROM.Shared.Store (ZMod 7) (Word 16) Nat :=
  (((g, pk), managed, live), saved, remaining)

private def groupConfig : Signing.Enumerated.Configuration 16 Nat (ZMod 7) (ZMod 7) where
  sampler := params
  message := config.message
  point := PrivateSampler.Enumerated.scalar params
  capacityPred := 2
  countFits := by decide
  storageFits := by decide
private theorem original_sampler {A : Type} (caller : Pass.Caller groupConfig A) (ops : Handler.Operations groupConfig)
    (law : Handler.SigningLaw groupConfig ops.signing)
    (fuel : Nat) (witness : Pass.Caller.Source groupConfig caller fuel) (value : Pass.Initialization.Input groupConfig)
    (room : Pass.Initialization.admitted groupConfig fuel value) :
    Pass.observed groupConfig <$> Pass.source groupConfig caller ops fuel value =
      (fun result => (some result.1, result.2)) <$> Schnorr.ListROM.Shared.tapeRun
        ((Schnorr.ListROM.passWith law.target
          (Subtype.val <$> witness.program (witness.inputView (Pass.Initialization.start groupConfig value).1))).run
            (value.2.val, [], [])) value.1.val := by
  have same : PrivateSampler.Enumerated.sampleable groupConfig.sampler = FinEnum.SampleableType (ZMod 7) :=
    PrivateSampler.Enumerated.sampleable_finEnum 12 (by decide) (by decide) (by decide)
  have original := Pass.source_tapeRun groupConfig caller ops law fuel witness value room
  rw [same] at original
  exact original

open Lean in
run_cmd do
  let saved : List (Schnorr.TapeCell (ZMod 7)) := [(3, 0, 1)]
  let replay : List (Schnorr.TapeCell (ZMod 7)) := [(1, 3, 0), (9, 0, 10), (8, 0, 6)]
  unless run true random 0 3 5 saved replay [88] ==
      some (some (some ((2, 5, 0), 3), store 3 5 [] [((2, 5), 3)] saved [(9, 0, 10), (8, 0, 6)]),
        [], [88], #[77], 4, 91, 9, true, true) do
    throwError "initialized immediate return lost the public key, original tapes or final replay hash"
  unless run false random 0 3 5 saved replay [88] ==
      some (some (none, store 3 5 [] [] saved replay), [], [88], #[77], 4, 91, 9, true, true) do
    throwError "initialized cutoff must keep tapes and empty caches without hashing"
  for fuel in [1, 2] do
    unless run false random fuel 3 5 saved replay [88] ==
        some (some (some ((2, 5, 0), 3), store 3 5 [] [((2, 5), 3)] saved [(8, 0, 6)]),
          [], [88], #[77], 4, 91, 9, true, true) do
      throwError "pass failed private replay followed by final hashing or continued after early return"
  unless run true random 0 9 11 [] [] [6, 0, 88] ==
      some (some (some ((2, 11, 0), 0), store 9 11 [] [((2, 11), 0)] [(1, 0, 0)] []),
        [.output 6, .invoke, .input 6, .input 0], [88], #[77], 4, 91, 9, true, true) do
    throwError "pass setup must load runtime generator/public key and preserve a zero fresh challenge"
  unless run false random 1 3 5 [] [] [7, 4, 6, 2, 88] ==
      some (some (some ((2, 5, 0), 2), store 3 5 [] [((2, 5), 2)] [(9, 0, 4), (1, 2, 0)] []),
        [.output 7, .invoke, .input 7, .input 4, .output 6, .invoke, .input 6, .input 2], [88], #[77], 4, 91, 9, true, true) do
    throwError "pass must compose caller randomness and fresh final hashing with one complete store"
  unless run false hashed 1 3 5 [] [] [6, 3, 88] ==
      some (some (some ((2, 5, 0), 3), store 3 5 [((2, 5), 3)] [((2, 5), 3)] [(1, 3, 0)] []),
        [.output 6, .invoke, .input 6, .input 3], [88], #[77], 4, 91, 9, true, true) do
    throwError "terminal must reuse the caller's LIVE entry without drawing a second challenge"
  unless run false signed 1 3 5 [] [] [6, 2, 6, 5, 6, 4, 88] ==
      some (some (some ((2, 5, 0), 4), store 3 5 [((2, 5), 2)] [((2, 5), 4)] [(8, 0, 2), (8, 0, 5), (1, 4, 0)] []),
        [.output 6, .invoke, .input 6, .input 2, .output 6, .invoke, .input 6, .input 5, .output 6, .invoke, .input 6, .input 4],
        [88], #[77], 4, 91, 9, true, true) do
    throwError "terminal must use LIVE rather than a conflicting signature-programmed managed entry"
  unless run false random 1 3 5 [] [] [7, 4] == none && run true random 0 3 5 [] [] [6] == none do
    throwError "a complete pass accepted an incomplete final oracle reply"
  unless run false random 3 3 5 [] [] [] == none &&
      run true random 0 3 5 (List.replicate 6 (3, 0, 1)) [] [] == none do
    throwError "pass accepted insufficient initial cache or saved-tape reserve"
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``Pass.called_ready, ``Pass.finish_refines, ``Pass.finish_preserves_config,
      ``Pass.finish_source_original, ``Pass.finish_observe_original, ``Pass.finish_time, ``Pass.finish_words,
      ``Pass.finish_names, ``Pass.finish_descriptionFits, ``Pass.finish_resources,
      ``Pass.Initialization.parts_bytes, ``Pass.Initialization.reserved, ``Pass.Initialization.time, ``Pass.Initialization.words,
      ``Pass.refines, ``Pass.preserves_config, ``Pass.source_original, ``Pass.source_tapeRun, ``Pass.observe_original,
      ``Pass.time, ``Pass.words, ``Pass.names, ``Pass.descriptionFits, ``Pass.resources,
      ``Pass.reply_injective, ``Pass.representedReply_eq, ``Pass.Caller.Source.ofCaller_run, ``original_sampler,
      ``PrivateHandler.tape_lengths, ``PrivateSampler.Service.tape_lengths, ``PrivateSampler.Pair.tape_lengths,
      ``Handler.tape_lengths, ``CallerHandler.tape_lengths, ``Caller.tape_lengths, ``Terminal.tape_lengths,
      ``Pass.finish_tape_lengths, ``Pass.tape_lengths, ``Pass.execution_tape_lengths] do
    for dependency in (← collectAxioms name) do
      unless dependency ∈ allowed do throwError "unexpected axiom {dependency} in {name}"

end SignaturesTest.CaliperSchnorrROMPass

