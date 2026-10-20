import Signatures.Runtime.Caliper.SchnorrROMFinalHashBounds
import Lean

open Caliper OracleComp OracleSpec Signatures.Runtime Signatures.Runtime.CaliperBackend BoundedSource
namespace SignaturesTest.CaliperSchnorrROMFinalHash
open SchnorrROMTape SchnorrROM

private instance : Fact (Nat.Prime 7) := ⟨by decide⟩
private def baseParams : PrivateSampler.Enumerated.Parameters 16 (ZMod 7) :=
  PrivateSampler.Enumerated.Parameters.ofFinEnum 16 (ZMod 7) 3 (by decide) (by decide) (by decide)
private def params (swapped : Bool) : PrivateSampler.Enumerated.Parameters 16 (ZMod 7) :=
  { baseParams with index := if swapped then baseParams.index.trans (Equiv.swap 0 1) else baseParams.index }
private def config (swapped : Bool) : Signing.Enumerated.Configuration 16 Nat (ZMod 7) (ZMod 7) where
  sampler := params swapped
  message := Layout.counter 16 256 (by decide) (by decide)
  point := PrivateSampler.Enumerated.scalar baseParams
  capacityPred := 1
  countFits := by decide
  storageFits := by change 4352 < 65536; decide

private instance (swapped : Bool)
    (value : (Nat × ZMod 7) × Schnorr.ListROM.Shared.Store (ZMod 7) (ZMod 7) Nat) :
    Decidable ((FinalHash.input (config swapped)).valid value) := by
  change Decidable (((value.1.1 < 256 ∧ True) ∧
    (((True ∧ True) ∧
      (value.2.1.2.1.length ≤ 2 ∧ ∀ entry ∈ value.2.1.2.1, (entry.1.1 < 256 ∧ True) ∧ True) ∧
      (value.2.1.2.2.length ≤ 2 ∧ ∀ entry ∈ value.2.1.2.2, (entry.1.1 < 256 ∧ True) ∧ True)) ∧
      (value.2.2.1.length ≤ 3 ∧ ∀ cell ∈ value.2.2.1, cell.1 < 65536 ∧ True ∧ cell.2.2 < 65536) ∧
      (value.2.2.2.length ≤ 3 ∧ ∀ cell ∈ value.2.2.2, cell.1 < 65536 ∧ True ∧ cell.2.2 < 65536))) ∧
    ((lookupValue value.1 0 value.2.1.2.2).1 = false → value.2.1.2.2.length ≤ 1))
  infer_instance

private def managed : Signing.Table Nat (ZMod 7) (ZMod 7) := [((2, 3), 6), ((1, 1), 2)]
private def saved : List (Schnorr.TapeCell (ZMod 7)) := [(3, 0, 1), (8, 0, 2)]
private def remaining : List (Schnorr.TapeCell (ZMod 7)) := [(8, 0, 20), (1, 5, 0), (9, 0, 4)]
private def privateOnly : List (Schnorr.TapeCell (ZMod 7)) := [(8, 0, 20), (9, 0, 4)]
private def live : Signing.Table Nat (ZMod 7) (ZMod 7) := [((1, 1), 4)]
private def store (live : Signing.Table Nat (ZMod 7) (ZMod 7))
    (saved remaining : List (Schnorr.TapeCell (ZMod 7))) : Schnorr.ListROM.Shared.Store (ZMod 7) (ZMod 7) Nat :=
  (((2, 4), managed, live), saved, remaining)

private def run (swapped : Bool) (key : Nat × ZMod 7) (live : Signing.Table Nat (ZMod 7) (ZMod 7))
    (saved remaining : List (Schnorr.TapeCell (ZMod 7))) (replies : List (Word 16)) := do
  let raw := (key, store live saved remaining)
  let value : (FinalHash.input (config swapped)).Value ← if valid : (FinalHash.input (config swapped)).valid raw then
    some ⟨raw, valid⟩ else none
  if ¬saved.length < 3 then none else do
    let initial := (FinalHash.input (config swapped)).representation.initial value
    let before := { initial with
      regs := fun r => if r = 99 then 91 else initial.regs r
      bufs := fun b => if b = 200 then #[77] else initial.bufs b
      caps := fun b => if b = 200 then 4 else initial.caps b
      tapePos := 9 }
    let result ← WordIO.run .unit RandomTape.zero 1000000
      ((FinalHash.code (config swapped)).lower (Fresh.port (config swapped).handler.sampler.tape)) before replies
    pure (((FinalHash.output (config swapped)).representation.encoding.decode (result.state.bufs 0).toList).map Subtype.val,
      result.trace, result.remaining, result.state.bufs 200, result.state.caps 200, result.state.regs 99,
      result.state.tapePos, (List.range 30).all (fun i => result.state.caps (i + 1) == 0),
      decide (result.time ≤ FinalHash.timeBudget (config swapped)))

private def prepareSwapped := do
  let raw := ((2, (3 : ZMod 7)), store live saved privateOnly)
  let value : (FinalHash.input (config true)).Value ← if valid : (FinalHash.input (config true)).valid raw then
    some ⟨raw, valid⟩ else none
  let result ← Caliper.run .unit RandomTape.zero 10000 (FinalHash.prepare (config true)).code
    ((FinalHash.input (config true)).representation.initial value)
  pure ((result.1.bufs 0)[2]?.getD 0)

private theorem matches_original (value : (FinalHash.input (config false)).Value) (valid : FinalHash.ready (config false) value) :
    Subtype.val <$> FinalHash.source (config false) value =
      (Schnorr.ListROM.Shared.interpret
        (Schnorr.ListROM.finalHash (G₂ := ZMod 7) (K := Nat) value.val.1)).run value.val.2 := by
  have same : PrivateSampler.Enumerated.sampleable (config false).sampler = FinEnum.SampleableType (ZMod 7) :=
    PrivateSampler.Enumerated.sampleable_finEnum 3 (by decide) (by decide) (by decide)
  have original := FinalHash.source_original (G₂ := ZMod 7) (K := Nat) (config false) value valid
  rw [same] at original
  exact original

open Lean in
run_cmd do
  let full : Signing.Table Nat (ZMod 7) (ZMod 7) := [((1, 1), 4), ((2, 3), 0)]
  unless run false (2, 3) full saved remaining [88] ==
      some (some (0, store full saved remaining), [], [88], #[77], 4, 91, 9, true, true) do
    throwError "final hash must return LIVE's zero and preserve the distinct managed answer/configuration/tapes"
  let duplicates : Signing.Table Nat (ZMod 7) (ZMod 7) := [((2, 3), 1), ((2, 3), 5)]
  unless run false (2, 3) duplicates saved remaining [] ==
      some (some (1, store duplicates saved remaining), [], [], #[77], 4, 91, 9, true, true) do
    throwError "final hash must preserve the first LIVE entry on duplicate-key hits"
  unless run false (2, 3) live saved remaining [88] ==
      some (some (5, store (((2, 3), 5) :: live) saved privateOnly), [], [88], #[77], 4, 91, 9, true, true) do
    throwError "final hash miss must consume public replay and insert only in LIVE"
  for answer in [(0 : Word 16), 3, 6] do
    let field : ZMod 7 := answer.toNat
    unless run false (2, 3) live saved privateOnly [6, answer, 88] ==
        some (some (field, store (((2, 3), field) :: live) (saved ++ [(1, field, 0)]) privateOnly),
          [.output 6, .invoke, .input 6, .input answer], [88], #[77], 4, 91, 9, true, true) do
      throwError "fresh final hash must fill the last LIVE/tape slots and preserve managed/configuration"
  unless prepareSwapped == some 1 do
    throwError "final-hash preparation assumed that scalar zero has word index zero"
  unless run true (2, 3) live saved privateOnly [6, 0, 88] ==
      some (some (1, store (((2, 3), 1) :: live) (saved ++ [(1, 1, 0)]) privateOnly),
        [.output 6, .invoke, .input 6, .input 0], [88], #[77], 4, 91, 9, true, true) do
    throwError "final hash lost the nonidentity scalar encoding across retained state"
  unless run false (2, 3) live saved privateOnly [] == none && run false (2, 3) live saved privateOnly [6] == none do
    throwError "final hash miss succeeded without a complete oracle reply"
  unless run false (3, 2) full saved remaining [] == none do
    throwError "final hash miss accepted a full LIVE table"
  unless run false (2, 3) live (saved ++ [(1, 0, 0)]) [] [6, 3] == none do
    throwError "final hash accepted a missing tape reservation"
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``FinalHash.refines, ``FinalHash.source_value, ``FinalHash.source_original,
      ``FinalHash.observe_original, ``FinalHash.preserves_config, ``FinalHash.preserves_managed,
      ``FinalHash.live_length, ``FinalHash.reserved_after,
      ``FinalHash.time_bound, ``FinalHash.code_bound, ``FinalHash.names, ``FinalHash.buffers,
      ``FinalHash.descriptionFits, ``FinalHash.resources, ``matches_original] do
    for dependency in (← collectAxioms name) do
      unless dependency ∈ allowed do throwError "unexpected axiom {dependency} in {name}"

end SignaturesTest.CaliperSchnorrROMFinalHash
