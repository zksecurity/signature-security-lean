import Proofs.Runtime.Caliper.SchnorrROMHashCacheSource
import Lean

open Caliper OracleComp OracleSpec Signatures.Runtime Signatures.Runtime.CaliperBackend BoundedSource
namespace SignaturesTest.CaliperSchnorrROMHashCache
open SchnorrROMTape SchnorrROM

private def config : Signing.Enumerated.Configuration 16 Nat (ZMod 7) Nat where
  sampler := PrivateSampler.Enumerated.Parameters.ofFinEnum 16 (ZMod 7) 3 (by decide) (by decide) (by decide)
  message := Layout.counter 16 256 (by decide) (by decide)
  point := Layout.counter 16 256 (by decide) (by decide)
  capacityPred := 1
  countFits := by decide
  storageFits := by decide

private theorem valid_iff (key : Nat × Nat) (entries : List ((Nat × Nat) × ZMod 7)) :
    (HashCache.model config).cache.input.valid (key, 0, entries, ()) ↔
      (key.1 < 256 ∧ key.2 < 256 ∧ entries.length ≤ 2 ∧ ∀ entry ∈ entries, entry.1.1 < 256 ∧ entry.1.2 < 256) ∧
        ((lookupValue key 0 entries).1 = false → entries.length ≤ 1) := by
  change (((key.1 < 256 ∧ key.2 < 256) ∧ True ∧
    (entries.length ≤ 2 ∧ ∀ entry ∈ entries, (entry.1.1 < 256 ∧ entry.1.2 < 256) ∧ True) ∧ True) ∧ _) ↔ _
  simp only [and_true, true_and]
  tauto

private def request (key : Nat × Nat) (entries : List ((Nat × Nat) × ZMod 7)) :
    Option (HashCache.model config).cache.input.Value :=
  if valid : (key.1 < 256 ∧ key.2 < 256 ∧ entries.length ≤ 2 ∧ ∀ entry ∈ entries, entry.1.1 < 256 ∧ entry.1.2 < 256) ∧
      ((lookupValue key 0 entries).1 = false → entries.length ≤ 1) then
    some ⟨(key, 0, entries, ()), (valid_iff key entries).mpr valid⟩
  else none

private def tapes (saved remaining : List (Schnorr.TapeCell (ZMod 7))) : Option (Read.tapes config.handler.sampler.tape).Value :=
  if valid : (saved.length ≤ 3 ∧ ∀ cell ∈ saved, cell.1 < 65536 ∧ cell.2.2 < 65536) ∧
      (remaining.length ≤ 3 ∧ ∀ cell ∈ remaining, cell.1 < 65536 ∧ cell.2.2 < 65536) then
    some ⟨(saved, remaining), by
      change (saved.length ≤ 3 ∧ ∀ cell ∈ saved, cell.1 < 65536 ∧ True ∧ cell.2.2 < 65536) ∧
        (remaining.length ≤ 3 ∧ ∀ cell ∈ remaining, cell.1 < 65536 ∧ True ∧ cell.2.2 < 65536)
      simpa only [true_and] using valid⟩
  else none

private def run (key : Nat × Nat) (entries : List ((Nat × Nat) × ZMod 7))
    (saved remaining : List (Schnorr.TapeCell (ZMod 7))) (replies : List (Word 16)) := do
  let req ← request key entries
  let state ← tapes saved remaining
  if ¬state.val.1.length < config.sampler.capacity then none else do
    let initial := (HashCache.model config).input.initial (req, state)
    let before := { initial with
      regs := fun r => if r = 99 then 91 else initial.regs r
      bufs := fun b => if b = 200 then #[77] else initial.bufs b
      caps := fun b => if b = 200 then 4 else initial.caps b
      tapePos := 9 }
    let result ← WordIO.run .unit RandomTape.zero 1000000
      ((HashCache.code config).lower (Fresh.port config.handler.sampler.tape)) before replies
    let decoded := ((HashCache.model config).output.encoding.decode (result.state.bufs 0).toList).map
      (fun value : (CacheRead.output (HashCache.model config).cache).Value × (Read.tapes config.handler.sampler.tape).Value =>
        (value.1.val, value.2.val))
    pure (decoded, result.trace, result.remaining, result.state.bufs 200, result.state.caps 200,
      result.state.regs 99, result.state.tapePos, (List.range 30).all (fun i => result.state.caps (i + 1) == 0),
      decide (result.time ≤ HashCache.timeBudget config))

private def saved : List (Schnorr.TapeCell (ZMod 7)) := [(3, 0, 1), (8, 0, 2)]
private def remaining : List (Schnorr.TapeCell (ZMod 7)) := [(8, 0, 20), (1, 5, 0), (9, 0, 4)]
private def privateOnly : List (Schnorr.TapeCell (ZMod 7)) := [(8, 0, 20), (9, 0, 4)]
private def entries : List ((Nat × Nat) × ZMod 7) := [((1, 10), 4)]

-- These input/exit facts expose the invariant boundary tested below: the last
-- reserved cell exists before a fresh miss and is spent by the successful exit.
private def beforeLast : (Read.tapes config.handler.sampler.tape).Value :=
  ⟨(saved, privateOnly), by
    change (saved.length ≤ 3 ∧ ∀ cell ∈ saved, cell.1 < 65536 ∧ True ∧ cell.2.2 < 65536) ∧
      (privateOnly.length ≤ 3 ∧ ∀ cell ∈ privateOnly, cell.1 < 65536 ∧ True ∧ cell.2.2 < 65536)
    simp [saved, privateOnly]⟩
example : EnumeratedReplay.ready config.sampler beforeLast := by change 2 < 3; decide
example : ¬ (saved ++ [(1, (3 : ZMod 7), 0)]).length < config.sampler.capacity := by
  change ¬ 3 < 3
  decide

open Lean in
run_cmd do
  let full : List ((Nat × Nat) × ZMod 7) := [((1, 10), 4), ((2, 20), 0)]
  unless run (2, 20) full saved remaining [88] ==
      some (some ((0, full), saved, remaining), [], [88], #[77], 4, 91, 9, true, true) do
    throwError "full-cache zero hit must leave the replay state and external state untouched"
  let duplicates : List ((Nat × Nat) × ZMod 7) := [((2, 20), 6), ((2, 20), 1)]
  unless run (2, 20) duplicates saved remaining [] ==
      some (some ((6, duplicates), saved, remaining), [], [], #[77], 4, 91, 9, true, true) do
    throwError "cache hit did not preserve the first stored challenge"
  unless run (2, 20) entries saved remaining [88] ==
      some (some ((5, ((2, 20), 5) :: entries), saved, privateOnly), [], [88], #[77], 4, 91, 9, true, true) do
    throwError "hash miss must insert the replayed challenge and consume only its scalar-family cell"
  for answer in [(0 : Word 16), 3, 6] do
    let field : ZMod 7 := answer.toNat
    unless run (2, 20) entries saved privateOnly [6, answer, 88] ==
        some (some ((field, ((2, 20), field) :: entries), saved ++ [(1, field, 0)], privateOnly),
          [.output 6, .invoke, .input 6, .input answer], [88], #[77], 4, 91, 9, true, true) do
      throwError "fresh hash miss failed to fill the last cache/tape slots with exactly one scalar draw"
  unless run (2, 20) entries saved privateOnly [] == none && run (2, 20) entries saved privateOnly [6] == none do
    throwError "hash miss succeeded without a complete oracle reply"
  unless run (3, 30) full saved remaining [] == none do
    throwError "cache miss accepted a full table"
  unless run (2, 20) entries (saved ++ [(1, 0, 0)]) [] [6, 3] == none do
    throwError "hash miss accepted a tape without its required reservation"
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``StatefulCacheRead.refines_on, ``StatefulCacheRead.time_bound_on,
      ``EnumeratedReplay.draw_refines, ``EnumeratedReplay.draw_time, ``EnumeratedReplay.draw_source,
      ``HashCache.refines, ``HashCache.time_bound, ``HashCache.code_bound, ``HashCache.names,
      ``HashCache.buffers, ``HashCache.descriptionFits, ``HashCache.resources,
      ``HashCache.source_value, ``HashCache.source_original] do
    for dependency in (← collectAxioms name) do
      unless dependency ∈ allowed do throwError "unexpected axiom {dependency} in {name}"

end SignaturesTest.CaliperSchnorrROMHashCache
