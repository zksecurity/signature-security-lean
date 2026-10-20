import Signatures.Runtime.Caliper.SchnorrROMHashBounds
import Lean

open Caliper OracleComp OracleSpec Signatures.Runtime Signatures.Runtime.CaliperBackend BoundedSource
namespace SignaturesTest.CaliperSchnorrROMHash
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
    Decidable ((Hash.input (config swapped)).valid value) := by
  change Decidable (((value.1.1 < 256 ∧ True) ∧
    (((True ∧ True) ∧
      (value.2.1.2.1.length ≤ 2 ∧ ∀ entry ∈ value.2.1.2.1, (entry.1.1 < 256 ∧ True) ∧ True) ∧
      (value.2.1.2.2.length ≤ 2 ∧ ∀ entry ∈ value.2.1.2.2, (entry.1.1 < 256 ∧ True) ∧ True)) ∧
      (value.2.2.1.length ≤ 3 ∧ ∀ cell ∈ value.2.2.1, cell.1 < 65536 ∧ True ∧ cell.2.2 < 65536) ∧
      (value.2.2.2.length ≤ 3 ∧ ∀ cell ∈ value.2.2.2, cell.1 < 65536 ∧ True ∧ cell.2.2 < 65536))) ∧
    ((lookupValue value.1 0 value.2.1.2.1).1 = false → value.2.1.2.1.length ≤ 1))
  infer_instance

private instance (swapped : Bool) (value : (Hash.input (config swapped)).Value) :
    Decidable (Hash.ready (config swapped) value) := by
  change Decidable (cacheMap value.val.2.1.2.1 value.val.1 = none →
    ((lookupValue value.val.1 0 value.val.2.1.2.2).1 = false → value.val.2.1.2.2.length ≤ 1) ∧
      value.val.2.2.1.length < 3)
  infer_instance

private def managed : Signing.Table Nat (ZMod 7) (ZMod 7) := [((1, 1), 2)]
private def saved : List (Schnorr.TapeCell (ZMod 7)) := [(3, 0, 1), (8, 0, 2)]
private def remaining : List (Schnorr.TapeCell (ZMod 7)) := [(8, 0, 20), (1, 5, 0), (9, 0, 4)]
private def privateOnly : List (Schnorr.TapeCell (ZMod 7)) := [(8, 0, 20), (9, 0, 4)]
private def live : Signing.Table Nat (ZMod 7) (ZMod 7) := [((1, 1), 4)]
private def store (managed live : Signing.Table Nat (ZMod 7) (ZMod 7))
    (saved remaining : List (Schnorr.TapeCell (ZMod 7))) : Schnorr.ListROM.Shared.Store (ZMod 7) (ZMod 7) Nat :=
  (((2, 4), managed, live), saved, remaining)

private def run (swapped : Bool) (key : Nat × ZMod 7) (managed live : Signing.Table Nat (ZMod 7) (ZMod 7))
    (saved remaining : List (Schnorr.TapeCell (ZMod 7))) (replies : List (Word 16)) := do
  let raw := (key, store managed live saved remaining)
  let value : (Hash.input (config swapped)).Value ← if valid : (Hash.input (config swapped)).valid raw then
    some ⟨raw, valid⟩ else none
  if ¬Hash.ready (config swapped) value then none else do
    let initial := (Hash.input (config swapped)).representation.initial value
    let before := { initial with
      regs := fun r => if r = 99 then 91 else initial.regs r
      bufs := fun b => if b = 200 then #[77] else initial.bufs b
      caps := fun b => if b = 200 then 4 else initial.caps b
      tapePos := 9 }
    let result ← WordIO.run .unit RandomTape.zero 1000000
      ((Hash.code (config swapped)).lower (Fresh.port (config swapped).handler.sampler.tape)) before replies
    pure (((Hash.output (config swapped)).representation.encoding.decode (result.state.bufs 0).toList).map Subtype.val,
      result.trace, result.remaining, result.state.bufs 200, result.state.caps 200, result.state.regs 99,
      result.state.tapePos, (List.range 30).all (fun i => result.state.caps (i + 1) == 0),
      decide (result.time ≤ Hash.timeBudget (config swapped)))

private theorem matches_original (value : (Hash.input (config false)).Value) (valid : Hash.ready (config false) value) :
    Subtype.val <$> Hash.source (config false) value =
      (Schnorr.ListROM.Shared.interpret
        (Schnorr.ListROM.handler (G₂ := ZMod 7) (K := Nat) (.inl (.inr value.val.1)))).run value.val.2 := by
  have same : PrivateSampler.Enumerated.sampleable (config false).sampler = FinEnum.SampleableType (ZMod 7) :=
    PrivateSampler.Enumerated.sampleable_finEnum 3 (by decide) (by decide) (by decide)
  have original := Hash.source_original (G₂ := ZMod 7) (K := Nat) (config false) value valid
  rw [same] at original
  exact original

open Lean in
run_cmd do
  let fullManaged : Signing.Table Nat (ZMod 7) (ZMod 7) := [((2, 3), 0), ((1, 1), 2)]
  let fullLive : Signing.Table Nat (ZMod 7) (ZMod 7) := [((4, 4), 4), ((5, 5), 3)]
  let fullSaved := saved ++ [(1, (6 : ZMod 7), 0)]
  unless run false (2, 3) fullManaged fullLive fullSaved remaining [88] ==
      some (some (0, store fullManaged fullLive fullSaved remaining), [], [88], #[77], 4, 91, 9, true, true) do
    throwError "managed zero hit must bypass LIVE and replay even with full unrelated LIVE and saved tape"
  let duplicateManaged : Signing.Table Nat (ZMod 7) (ZMod 7) := [((2, 3), 1), ((2, 3), 5)]
  unless run false (2, 3) duplicateManaged live saved remaining [] ==
      some (some (1, store duplicateManaged live saved remaining), [], [], #[77], 4, 91, 9, true, true) do
    throwError "managed duplicate-key hit must preserve the first answer"
  let liveHit : Signing.Table Nat (ZMod 7) (ZMod 7) := [((1, 1), 4), ((2, 3), 0)]
  unless run false (2, 3) managed liveHit saved remaining [88] ==
      some (some (0, store (((2, 3), 0) :: managed) liveHit saved remaining), [], [88], #[77], 4, 91, 9, true, true) do
    throwError "LIVE zero hit must insert managed only and preserve both tapes"
  unless run false (2, 3) managed live saved remaining [88] ==
      some (some (5, store (((2, 3), 5) :: managed) (((2, 3), 5) :: live) saved privateOnly), [], [88], #[77], 4, 91, 9, true, true) do
    throwError "both-cache miss must consume one public replay cell and update both tables"
  for answer in [(0 : Word 16), 3, 6] do
    let field : ZMod 7 := answer.toNat
    unless run false (2, 3) managed live saved privateOnly [6, answer, 88] ==
        some (some (field, store (((2, 3), field) :: managed) (((2, 3), field) :: live)
          (saved ++ [(1, field, 0)]) privateOnly),
          [.output 6, .invoke, .input 6, .input answer], [88], #[77], 4, 91, 9, true, true) do
      throwError "fresh normal hash must fill the last table/tape slots with exactly one public query"
  unless run true (2, 3) managed live saved privateOnly [6, 0, 88] ==
      some (some (1, store (((2, 3), 1) :: managed) (((2, 3), 1) :: live)
        (saved ++ [(1, 1, 0)]) privateOnly),
        [.output 6, .invoke, .input 6, .input 0], [88], #[77], 4, 91, 9, true, true) do
    throwError "normal hash lost the nonidentity scalar encoding"
  unless run false (2, 3) managed live saved privateOnly [] == none &&
      run false (2, 3) managed live saved privateOnly [6] == none do
    throwError "hash miss succeeded without a complete oracle reply"
  unless run false (3, 2) fullManaged live saved remaining [] == none &&
      run false (2, 3) managed fullLive saved remaining [] == none &&
      run false (2, 3) managed live fullSaved [] [6, 3] == none do
    throwError "hash miss accepted exhausted managed/LIVE/tape capacity"
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``StatefulCacheRead.refines_on_miss, ``StatefulCacheRead.time_bound_on_miss,
      ``HashMiss.refines, ``HashMiss.source_finalHash, ``HashMiss.preserves_key,
      ``HashMiss.time_bound, ``HashMiss.code_bound, ``HashMiss.names, ``HashMiss.buffers,
      ``HashMiss.descriptionFits, ``HashMiss.resources,
      ``Hash.refines, ``Hash.source_value, ``Hash.source_original, ``Hash.observe_original,
      ``Hash.postcondition, ``Hash.reserved_after,
      ``Hash.time_bound, ``Hash.code_bound, ``Hash.names, ``Hash.buffers,
      ``Hash.descriptionFits, ``Hash.resources, ``matches_original] do
    for dependency in (← collectAxioms name) do
      unless dependency ∈ allowed do throwError "unexpected axiom {dependency} in {name}"

end SignaturesTest.CaliperSchnorrROMHash
