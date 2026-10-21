import Signatures.Runtime.Caliper.SchnorrROMReplayChallengeChecked
import Lean

open Caliper Signatures.Runtime Signatures.Runtime.CaliperBackend BoundedSource
namespace SignaturesTest.CaliperSchnorrROMReplayChallenge
open SchnorrROMTape SchnorrROM

private def params : PrivateSampler.Enumerated.Parameters 16 (ZMod 7) :=
  PrivateSampler.Enumerated.Parameters.ofFinEnum 16 (ZMod 7) 10 (by decide) (by decide) (by decide)
private def config : Signing.Enumerated.Configuration 16 Nat (ZMod 7) (Word 16) where
  sampler := params
  message := Layout.counter 16 256 (by decide) (by decide)
  point := Layout.all (wordRepresentation 16 (by decide))
  capacityPred := 2
  countFits := by decide
  storageFits := by decide
private abbrev Store := Schnorr.ListROM.Shared.Store (ZMod 7) (Word 16) Nat
private instance (value : Store) : Decidable (config.handler.store.valid value) := by
  change Decidable ((((True ∧ True) ∧
    (value.1.2.1.length ≤ 3 ∧ ∀ entry ∈ value.1.2.1, (entry.1.1 < 256 ∧ True) ∧ True) ∧
    (value.1.2.2.length ≤ 3 ∧ ∀ entry ∈ value.1.2.2, (entry.1.1 < 256 ∧ True) ∧ True)) ∧
    (value.2.1.length ≤ 10 ∧ ∀ cell ∈ value.2.1, cell.1 < 65536 ∧ True ∧ cell.2.2 < 65536) ∧
    (value.2.2.length ≤ 10 ∧ ∀ cell ∈ value.2.2, cell.1 < 65536 ∧ True ∧ cell.2.2 < 65536)))
  infer_instance

private def run (returned : Bool) (slot : Fin 65536) (replies : List (Word 16)) := do
  let forge : (ForgeryHash.forgery config).Value := ⟨(2, 0, 0), by change 2 < 256; decide, trivial, trivial⟩
  let first : Terminal.Output config :=
    (if returned then .inr (forge, ⟨6, trivial⟩) else .inl (),
      ⟨(((3, 0), [((2, 3), 6)], [((4, 5), 1)]), [(3, 0, 5), (1, 3, 0), (1, 4, 0)], [(1, 6, 0)]), by decide⟩)
  let value : ReplayChallenge.Input config := (⟨slot.val, slot.isLt⟩, first)
  let initial := (ReplayChallenge.input config).initial value
  let before := { initial with bufs := fun i => if i = 200 then #[77] else initial.bufs i
                               caps := fun i => if i = 200 then 4 else initial.caps i
                               regs := fun i => if i = 99 then 91 else initial.regs i
                               tapePos := 9 }
  let result ← WordIO.run .unit RandomTape.zero 100000
    ((ReplayChallenge.Checked.program config).lower (Fresh.port config.handler.sampler.tape)) before replies
  pure (((ReplayChallenge.Guard.output config).encoding.decode (result.state.bufs 0).toList).map
      (fun answer : config.handler.sampler.tape.boolean.Value × ReplaySecond.Request config =>
        (answer.1.val, answer.2.1.1.val, answer.2.1.2.val.val,
          (ReplaySecond.first config).encoding.encode answer.2.2 == (ReplaySecond.first config).encoding.encode first)),
    result.trace, result.remaining, result.state.bufs 200, result.state.caps 200, result.state.regs 99,
    result.state.tapePos, (List.range 30).all (fun i => result.state.caps (i + 1) == 0),
    decide (result.time ≤ ReplayChallenge.Checked.timeBudget config))

open Lean in
run_cmd do
  for (returned, slot, replacement, same) in [(true, (0 : Fin 65536), (3 : Word 16), true),
      (true, 0, 0, false), (true, 0, 4, false), (true, 0, 6, false),
      (true, 1, 4, true), (true, 1, 3, false), (true, 1, 6, false),
      (false, 0, 3, true), (false, 1, 4, true), (true, 65535, 0, false)] do
    unless run returned slot [6, replacement, 88] ==
        some (some (same, slot.val, replacement.toNat, true),
          [.output 6, .invoke, .input 6, .input replacement], [88], #[77], 4, 91, 9, true, true) do
      throwError "draw/guard used the forgery or remaining tape, lost a frame, or failed its trace/scratch/time bound"
  unless run true 0 [6] == none do throwError "draw/guard accepted an incomplete uniform reply"
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``ReplayChallenge.Guard.prepare_bytes, ``ReplayChallenge.Guard.realizer,
      ``ReplayChallenge.Guard.source_original, ``ReplayChallenge.Guard.names, ``ReplayChallenge.Guard.buffers,
      ``ReplayChallenge.Guard.time, ``ReplayChallenge.Guard.words, ``ReplayChallenge.Checked.refines,
      ``ReplayChallenge.Checked.retains_first, ``ReplayChallenge.Checked.source_original, ``ReplayChallenge.Checked.time, ``ReplayChallenge.Checked.words,
      ``ReplayChallenge.Checked.names, ``ReplayChallenge.Checked.buffers, ``ReplayChallenge.Checked.descriptionFits,
      ``ReplayChallenge.Checked.resources] do
    for dependency in (← collectAxioms name) do
      unless dependency ∈ allowed do throwError "unexpected axiom {dependency} in {name}"

end SignaturesTest.CaliperSchnorrROMReplayChallenge
