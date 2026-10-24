import Proofs.Runtime.Caliper.SchnorrROMEnumeratedReplay
import Lean

open Caliper OracleComp OracleSpec Signatures.Runtime Signatures.Runtime.CaliperBackend BoundedSource
namespace SignaturesTest.CaliperSchnorrROMEnumeratedReplay
open SchnorrROMTape PrivateSampler.Enumerated

private def params : Parameters 16 (ZMod 7) := Parameters.ofFinEnum 16 (ZMod 7) 6 (by decide) (by decide) (by decide)
private theorem canonical_draw : Subtype.val <$> Direct.source params = ($ᵗ (ZMod 7) : ProbComp (ZMod 7)) :=
  Direct.uniform_finEnum 6 (by decide) (by decide) (by decide)
private theorem canonical_oracle : Fresh.sample (tape params) (Direct.source params) =
    _root_.Schnorr.LazyROM.sample (F := ZMod 7) := by
  have same := sampleable_finEnum (w := 16) (F := ZMod 7) 6 (by decide) (by decide) (by decide)
  have sampled := EnumeratedReplay.sample_eq params
  unfold params at sampled
  rw [same] at sampled
  exact sampled

private def store (saved remaining : List (Schnorr.TapeCell (ZMod 7))) : Option (Read.store (tape params)).Value :=
  if valid : saved.length < 6 ∧ remaining.length ≤ 6 ∧
      (∀ cell ∈ saved, cell.1 < 65536 ∧ cell.2.2 < 65536) ∧
      (∀ cell ∈ remaining, cell.1 < 65536 ∧ cell.2.2 < 65536) then
    some ⟨(saved, remaining), by
      change ((saved.length ≤ 6 ∧ ∀ cell ∈ saved, cell.1 < 65536 ∧ True ∧ cell.2.2 < 65536) ∧ saved.length < 6) ∧
        (remaining.length ≤ 6 ∧ ∀ cell ∈ remaining, cell.1 < 65536 ∧ True ∧ cell.2.2 < 65536)
      simpa only [true_and] using And.intro (And.intro (And.intro (by omega) valid.2.2.1) valid.1) (And.intro valid.2.1 valid.2.2.2)⟩
  else none

private def run {A B : Type} (input : Layout 16 A) (output : Layout 16 B)
    (program : Interactive.Code 16) (time : Nat) (value : input.Value) (replies : List (Word 16)) := do
  let initial := input.representation.initial value
  let before := { initial with bufs := fun b => if b = 200 then #[77] else initial.bufs b
                               caps := fun b => if b = 200 then 4 else initial.caps b
                               regs := fun r => if r = 99 then 91 else initial.regs r
                               tapePos := 9 }
  let result ← WordIO.run .unit RandomTape.zero 100000 (program.lower (Fresh.port (tape params))) before replies
  pure ((output.representation.encoding.decode (result.state.bufs 0).toList).map Subtype.val,
    result.trace, result.remaining, result.state.bufs 200, result.state.caps 200, result.state.regs 99,
    result.state.tapePos, (List.range 20).all (fun i => result.state.caps (i + 1) == 0), decide (result.time ≤ time))

private def runScalar (saved remaining : List (Schnorr.TapeCell (ZMod 7))) (replies : List (Word 16)) := do
  let value ← store saved remaining
  run (Read.store (tape params)) (Reply.scalarOutput (tape params)) (EnumeratedReplay.scalarCode params)
    (Caller.scalarTime (tape params) trivial 26) value replies

private def runPrivate (range : Fin 65534) (saved remaining : List (Schnorr.TapeCell (ZMod 7))) (replies : List (Word 16)) := do
  let value ← store saved remaining
  run (Caller.privateInput (tape params)) (Reply.privateOutput (tape params)) (EnumeratedReplay.privateCode params)
    (Caller.privateTime (tape params) trivial 26) ⟨(range.val, value.val), range.isLt, value.property⟩ replies

private def saved : List (Schnorr.TapeCell (ZMod 7)) := [(3, 0, 1)]
private def privateOnly : List (Schnorr.TapeCell (ZMod 7)) := [(8, 0, 20), (9, 0, 10)]

-- The direct sampler also runs with a large field-index domain. Its description
-- and local execution bounds do not depend on enumerating that domain.
private def big : Parameters 32 (Fin (2 ^ 24)) where
  bound := 2 ^ 24 - 1
  index := finCongr (by decide)
  capacity := 6
  wordFits := by decide
  rangeFits := by decide
  storageFits := by decide
private theorem big_stored : ((Direct.code big).lower (Fresh.port (tape big))).descriptionWords ≤ 125 := Direct.code_words big
private def bigRun := do
  let result ← WordIO.run .unit RandomTape.zero 1000 ((Direct.code big).lower (Fresh.port (tape big)))
    ((tape big).unit.representation.initial ⟨(), trivial⟩) [2 ^ 24 - 1, 2 ^ 24 - 2, 88]
  pure (((scalar big).representation.encoding.decode (result.state.bufs 0).toList).map (fun value : (scalar big).Value => value.val.val),
    result.trace, result.remaining, decide (result.time ≤ 26))

open Lean in
run_cmd do
  for answer in [(0 : Word 16), 3, 6] do
    let field : ZMod 7 := answer.toNat
    let trace : List (WordIO.Event 16) := [.output 6, .invoke, .input 6, .input answer]
    unless run (tape params).unit (scalar params) (Direct.code params) 26 ⟨(), trivial⟩ [6, answer, 88] ==
        some (some field, trace, [88], #[77], 4, 91, 9, true, true) do
      throwError "direct scalar sampling changed the finite range, result, trace or external state"
    unless runScalar saved privateOnly [6, answer, 88] ==
        some (some (field, saved ++ [(1, field, 0)], privateOnly), trace, [88], #[77], 4, 91, 9, true, true) do
      throwError "fresh challenge must record one scalar cell and leave private replay cells untouched"
  unless runScalar saved [(8, 0, 20), (1, 0, 0), (9, 0, 10)] [88] ==
      some (some (0, saved, privateOnly), [], [88], #[77], 4, 91, 9, true, true) do
    throwError "replayed zero challenge was mistaken for a miss or consumed private randomness"
  unless runScalar saved [(1, 5, 0), (1, 2, 0)] [88] ==
      some (some (5, saved, [(1, 2, 0)]), [], [88], #[77], 4, 91, 9, true, true) do
    throwError "challenge replay did not consume only the first matching cell"
  unless runPrivate 6 saved [(1, 5, 0), (8, 0, 20)] [88] ==
      some (some (6, 6, saved, [(1, 5, 0)]), [], [88], #[77], 4, 91, 9, true, true) do
    throwError "private replay must normalize its natural payload and preserve the challenge cell"
  unless runPrivate 7 saved [(1, 5, 0)] [7, 4, 88] ==
      some (some (7, 4, saved ++ [(9, 0, 4)], [(1, 5, 0)]),
        [.output 7, .invoke, .input 7, .input 4], [88], #[77], 4, 91, 9, true, true) do
    throwError "private fresh query used the scalar sampler's fixed range or changed the challenge tape"
  let almostFull := List.replicate 5 (3, (0 : ZMod 7), 1)
  unless runScalar almostFull [] [6, 3, 88] ==
      some (some (3, almostFull ++ [(1, 3, 0)], []),
        [.output 6, .invoke, .input 6, .input 3], [88], #[77], 4, 91, 9, true, true) do
    throwError "fresh challenge did not respect its last reserved tape slot"
  unless runScalar (List.replicate 6 (3, 0, 1)) [] [6, 3] == none do
    throwError "fresh challenge accepted a store without its required reservation"
  unless runScalar saved [] [] == none && runScalar saved [] [6] == none && runPrivate 6 saved [] [] == none do
    throwError "fresh query succeeded without its complete oracle reply"
  unless bigRun == some (some (2 ^ 24 - 2),
      [.output (2 ^ 24 - 1), .invoke, .input (2 ^ 24 - 1), .input (2 ^ 24 - 2)], [88], true) do
    throwError "large-domain direct sampling exceeded its constant bound or changed the result"
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``Direct.refines, ``Direct.uniform, ``Direct.uniform_finEnum, ``Direct.within,
      ``Direct.time_bound, ``Direct.code_words, ``Direct.descriptionFits, ``big_stored,
      ``canonical_draw, ``canonical_oracle, ``EnumeratedReplay.private_source, ``EnumeratedReplay.scalar_source,
      ``EnumeratedReplay.private_observe, ``EnumeratedReplay.scalar_observe,
      ``EnumeratedReplay.private_within, ``EnumeratedReplay.scalar_within] do
    for dependency in (← collectAxioms name) do
      unless dependency ∈ allowed do throwError "unexpected axiom {dependency} in {name}"

end SignaturesTest.CaliperSchnorrROMEnumeratedReplay
