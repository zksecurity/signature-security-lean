import Signatures.Runtime.Caliper.SchnorrROMEnumeratedSigning
import Lean

open Caliper OracleComp OracleSpec Signatures.Runtime Signatures.Runtime.CaliperBackend BoundedSource
namespace SignaturesTest.CaliperSchnorrROMEnumeratedSampler
open SchnorrROMTape PrivateSampler.Enumerated

private instance : Fact (Nat.Prime 7) := ⟨by decide⟩
private def params : Parameters 16 (ZMod 7) := Parameters.ofFinEnum 16 (ZMod 7) 6 (by decide) (by decide) (by decide)
private theorem original_eq :
    Subtype.val <$> PrivateSampler.original (layout params) (caller params) 1 (terminates params) ⟨(), trivial⟩ =
      ($ᵗ (ZMod 7) : ProbComp (ZMod 7)) := samples_finEnum 6 (by decide) (by decide) (by decide) _
private theorem same_sampler : sampleable params = FinEnum.SampleableType (ZMod 7) :=
  sampleable_finEnum 6 (by decide) (by decide) (by decide)

private theorem source_eq (saved : PrivateSampler.Store (layout params)) (valid : PrivateSampler.Pair.ready (layout params) 1 saved) :
    Subtype.val <$> PrivateSampler.Pair.source (layout params) (caller params) trivial 1 saved = (do
      let first ← Schnorr.ListROM.Shared.tapeRun (Schnorr.privateImpl (F := ZMod 7) (.inr ())) saved.val
      (fun second => (first.1, second)) <$>
        Schnorr.ListROM.Shared.tapeRun (Schnorr.privateImpl (F := ZMod 7) (.inr ())) first.2) :=
  PrivateSampler.Pair.scalar_source (layout params) (caller params) trivial 1 (terminates params) original_eq saved valid

private def saved : List (Schnorr.TapeCell (ZMod 7)) := [(3, 0, 1)]
private def run (remaining : List (Schnorr.TapeCell (ZMod 7))) (replies : List (Word 16)) := do
  let value : PrivateSampler.Store (layout params) ←
    if valid : remaining.length ≤ 6 ∧ ∀ cell ∈ remaining, cell.1 < 65536 ∧ cell.2.2 < 65536 then
      some ⟨(saved, remaining), by
        constructor
        · change saved.length ≤ 6 ∧ ∀ cell ∈ saved, cell.1 < 65536 ∧ True ∧ cell.2.2 < 65536
          simp [saved]
        · change remaining.length ≤ 6 ∧ ∀ cell ∈ remaining, cell.1 < 65536 ∧ True ∧ cell.2.2 < 65536
          simpa only [true_and] using valid⟩
    else none
  let initial := (Read.tapes (tape params)).representation.initial value
  let before := { initial with bufs := fun b => if b = 200 then #[77] else initial.bufs b
                               caps := fun b => if b = 200 then 4 else initial.caps b
                               regs := fun r => if r = 99 then 91 else initial.regs r
                               tapePos := 9 }
  let program := PrivateSampler.Pair.code (layout params) (caller params) trivial 1
  let result ← WordIO.run .unit RandomTape.zero 1000000 (program.lower (Fresh.port (tape params))) before replies
  let decoded := ((PrivateSampler.Pair.output (layout params)).representation.encoding.decode (result.state.bufs 0).toList).map Subtype.val
  pure (decoded, result.trace, result.remaining, result.state.bufs 200, result.state.caps 200,
    result.state.regs 99, result.state.tapePos, (List.range 30).all (fun i => result.state.caps (i + 1) == 0),
    decide (result.time ≤ PrivateSampler.Pair.timeBudget (layout params) trivial 38 16 1))

private def normalizedInput : Unit × PrivateSampler.Response (layout params) :=
  ((), ⟨(20, 20), by change (20 < 65534 ∧ 20 < 65536) ∧ 20 ≤ 20; decide⟩)
private def normalizeRun :=
  let before := (CallerStep.resume (PrivateSampler.step (layout params))).initial normalizedInput
  (Caliper.run .unit RandomTape.zero 1000 (continuation params).code before).map fun result =>
    (result.1.bufs 0, decide (result.2.1 ≤ 38))

-- The local description has the same bound with more than sixteen million
-- possible scalars. Neither generation nor execution constructs that domain.
private def big : Parameters 32 (Fin (2 ^ 24)) where
  bound := 2 ^ 24 - 1
  index := finCongr (by decide)
  capacity := 6
  wordFits := by decide
  rangeFits := by decide
  storageFits := by decide
private theorem big_stored : descriptionWords (continuation big).code ≤ 161 := continuation_words big
private def bigInput : Unit × PrivateSampler.Response (layout big) :=
  ((), ⟨(2 ^ 24 + 4, 2 ^ 24 + 4), by change (_ < 2 ^ 32 - 2 ∧ _ < 2 ^ 32) ∧ _ ≤ _; decide⟩)
private def bigRun :=
  let before := (CallerStep.resume (PrivateSampler.step (layout big))).initial bigInput
  (Caliper.run .unit RandomTape.zero 1000 (continuation big).code before).map fun result =>
    (result.1.bufs 0, decide (result.2.1 ≤ 38))

-- The complete constructed caller also executes inside signing. Word points
-- exercise machine arithmetic; the source theorem separately ranges over groups.
private instance : SMul (ZMod 7) (Word 16) := ⟨fun scalar point => BitVec.ofNat 16 scalar.val * point⟩
private def signing : SchnorrROM.Signing.Enumerated.Configuration 16 Nat (ZMod 7) (Word 16) where
  sampler := params
  message := Layout.counter 16 256 (by decide) (by decide)
  point := Layout.all (wordRepresentation 16 (by decide))
  capacityPred := 2
  countFits := by decide
  storageFits := by decide
private def scale : Implementation .unit signing.handler.core.arithmetic.scaleArgs signing.handler.core.point (fun input => input.1 • input.2) where
  preserves _ _ := trivial
  program := ((WordBinary.realizer .unit .mul (by decide)).viewInput signing.handler.core.arithmetic.scaleArgs.representation
    (fun input => (BitVec.ofNat 16 input.val.1.val, input.val.2)) (fun _ => rfl)).viewOutput signing.handler.core.point.representation
      (fun input => ⟨input.val.1 • input.val.2, trivial⟩) (fun _ => rfl)
private def sub : Implementation .unit signing.handler.core.arithmetic.points signing.handler.core.point (fun input => input.1 - input.2) where
  preserves _ _ := trivial
  program := ((WordBinary.realizer .unit .sub (by decide)).viewInput signing.handler.core.arithmetic.points.representation
    (fun input => input.val) (fun _ => rfl)).viewOutput signing.handler.core.point.representation
      (fun input => ⟨input.val.1 - input.val.2, trivial⟩) (fun _ => rfl)
private theorem scaleBound : scale.BoundedBy 6 27 := ⟨fun _ => by change 6 ≤ 6; omega, by decide⟩
private theorem subBound : sub.BoundedBy 6 27 := ⟨fun _ => by change 6 ≤ 6; omega, by decide⟩
private theorem scaleNames : NamesBound scale.program.code 3 := ⟨by decide, by decide⟩
private theorem subNames : NamesBound sub.program.code 3 := ⟨by decide, by decide⟩
private def signingCode := SchnorrROM.Signing.Enumerated.code signing scale sub scaleNames.buffers subNames.buffers (by decide)
private theorem signingTime : Interactive.TimeBoundOn (SchnorrROM.Signing.Handler.ready signing.handler 1)
    (Fresh.port (tape params)) .unit signing.handler.input.representation signingCode
    (SchnorrROM.Signing.Handler.timeBudget signing.handler trivial 38 16 1 6 6) :=
  SchnorrROM.Signing.Enumerated.time_bound signing scale sub scaleNames.buffers subNames.buffers (by decide) scaleBound subBound
private instance (value : Nat × Schnorr.ListROM.Shared.Store (ZMod 7) (Word 16) Nat) : Decidable (signing.handler.input.valid value) := by
  change Decidable ((value.1 < 256 ∧
    (((True ∧ True) ∧ (value.2.1.2.1.length ≤ 3 ∧ ∀ entry ∈ value.2.1.2.1, (entry.1.1 < 256 ∧ True) ∧ True) ∧
      (value.2.1.2.2.length ≤ 3 ∧ ∀ entry ∈ value.2.1.2.2, (entry.1.1 < 256 ∧ True) ∧ True)) ∧
      (value.2.2.1.length ≤ 6 ∧ ∀ cell ∈ value.2.2.1, cell.1 < 65536 ∧ True ∧ cell.2.2 < 65536) ∧
      (value.2.2.2.length ≤ 6 ∧ ∀ cell ∈ value.2.2.2, cell.1 < 65536 ∧ True ∧ cell.2.2 < 65536))) ∧
    value.2.1.2.1.length ≤ 2)
  infer_instance
private def signingReplay : signing.handler.input.Value :=
  ⟨(7, ((3, 5), [((5, 6), 1)], [((7, 3), 0)]), saved, [(8, 0, 10), (8, 0, 20), (1, 4, 0)]), by decide⟩
private def signingFresh : signing.handler.input.Value :=
  ⟨(7, ((3, 5), [((5, 6), 1)], [((7, 3), 0)]), saved, [(1, 4, 0)]), by decide⟩
private def runSigning (input : signing.handler.input.Value) (replies : List (Word 16)) := do
  let before := signing.handler.input.representation.initial input
  let result ← WordIO.run .unit RandomTape.zero 1000000 (signingCode.lower (Fresh.port (tape params))) before replies
  let decoded := (signing.handler.output.representation.encoding.decode (result.state.bufs 0).toList).map Subtype.val
  pure (decoded, result.trace, result.remaining, (List.range 30).all (fun i => result.state.caps (i + 1) == 0),
    decide (result.time ≤ SchnorrROM.Signing.Handler.timeBudget signing.handler trivial 38 16 1 6 6))

open Lean in
run_cmd do
  let tail : List (Schnorr.TapeCell (ZMod 7)) := [(1, 4, 0)]
  unless run ([(8, 0, 10), (8, 0, 20)] ++ tail) [88] ==
      some (some (3, 6, saved, tail), [], [88], #[77], 4, 91, 9, true, true) do
    throwError "canonical field sampling did not replay both indices in order"
  unless run tail [6, 3, 6, 6, 88] ==
      some (some (3, 6, saved ++ [(8, 0, 3), (8, 0, 6)], tail),
        [.output 6, .invoke, .input 6, .input 3, .output 6, .invoke, .input 6, .input 6], [88], #[77], 4, 91, 9, true, true) do
    throwError "canonical field sampling did not save both fresh queries with the original family"
  unless run ([(8, 0, 10)] ++ tail) [6, 6, 88] ==
      some (some (3, 6, saved ++ [(8, 0, 6)], tail), [.output 6, .invoke, .input 6, .input 6], [88], #[77], 4, 91, 9, true, true) do
    throwError "canonical field sampling lost the replay/fresh boundary"
  unless run ([(9, 0, 5)] ++ tail) [6, 3, 6, 6, 88] ==
      some (some (3, 6, saved ++ [(8, 0, 3), (8, 0, 6)], [(9, 0, 5)] ++ tail),
        [.output 6, .invoke, .input 6, .input 3, .output 6, .invoke, .input 6, .input 6], [88], #[77], 4, 91, 9, true, true) do
    throwError "canonical sampling consumed a cell from another private query family"
  unless run ([(8, 0, 0), (8, 0, 0)] ++ tail) [88] ==
      some (some (0, 0, saved, tail), [], [88], #[77], 4, 91, 9, true, true) do
    throwError "canonical field sampling rejected zero"
  unless run tail [6, 3] == none do throwError "canonical sampling returned without its second reply"
  unless run (List.replicate 7 (8, 0, 0)) [] == none do throwError "oversized replay tape was admitted"
  unless normalizeRun == some (#[0, 6], true) do throwError "local caller did not execute modulo on an arbitrary represented reply"
  unless bigRun == some (#[0, 4], true) do throwError "large scalar domain changed the bounded local caller"
  unless runSigning signingReplay [88] ==
      some (some ((3, 6), ((3, 5), [((7, 3), 3), ((5, 6), 1)], [((7, 3), 0)]), saved, tail), [], [88], true, true) do
    throwError "constructed sampler did not feed both replayed field scalars into signing"
  unless runSigning signingFresh [6, 3, 6, 6, 88] ==
      some (some ((3, 6), ((3, 5), [((7, 3), 3), ((5, 6), 1)], [((7, 3), 0)]), saved ++ [(8, 0, 3), (8, 0, 6)], tail),
        [.output 6, .invoke, .input 6, .input 3, .output 6, .invoke, .input 6, .input 6], [88], true, true) do
    throwError "constructed signing lost fresh field scalars, LIVE or the shared tapes"
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``initialCode, ``continuation, ``caller, ``terminates, ``original_typed, ``original_scalar, ``samples,
      ``samples_finEnum, ``sampleable_finEnum, ``initial_time, ``continuation_time, ``continuation_words,
      ``pair_time, ``pair_names, ``pair_descriptionFits, ``source_eq, ``same_sampler, ``big_stored,
      ``SchnorrROM.Signing.Enumerated.source_original, ``SchnorrROM.Signing.Enumerated.observe_original,
      ``SchnorrROM.Signing.Enumerated.time_bound, ``SchnorrROM.Signing.Enumerated.names,
      ``SchnorrROM.Signing.Enumerated.code_bound, ``SchnorrROM.Signing.Enumerated.buffers,
      ``SchnorrROM.Signing.Enumerated.descriptionFits, ``signingTime] do
    for dependency in (← collectAxioms name) do
      unless dependency ∈ allowed do throwError "unexpected axiom {dependency} in {name}"

end SignaturesTest.CaliperSchnorrROMEnumeratedSampler
