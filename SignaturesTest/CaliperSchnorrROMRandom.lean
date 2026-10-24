import Proofs.Runtime.Caliper.SchnorrROMRandomBounds
import Lean

open Caliper OracleComp OracleSpec Signatures.Runtime Signatures.Runtime.CaliperBackend BoundedSource
namespace SignaturesTest.CaliperSchnorrROMRandom
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

private instance (swapped : Bool) (value : Nat × Schnorr.ListROM.Shared.Store (ZMod 7) (ZMod 7) Nat) :
    Decidable ((Random.input (config swapped)).valid value) := by
  change Decidable ((value.1 < 65534 ∧
    (((True ∧ True) ∧
      (value.2.1.2.1.length ≤ 2 ∧ ∀ entry ∈ value.2.1.2.1, (entry.1.1 < 256 ∧ True) ∧ True) ∧
      (value.2.1.2.2.length ≤ 2 ∧ ∀ entry ∈ value.2.1.2.2, (entry.1.1 < 256 ∧ True) ∧ True)) ∧
      (value.2.2.1.length ≤ 3 ∧ ∀ cell ∈ value.2.2.1, cell.1 < 65536 ∧ True ∧ cell.2.2 < 65536) ∧
      (value.2.2.2.length ≤ 3 ∧ ∀ cell ∈ value.2.2.2, cell.1 < 65536 ∧ True ∧ cell.2.2 < 65536))) ∧
    value.2.2.1.length < 3)
  infer_instance

private def managed : Signing.Table Nat (ZMod 7) (ZMod 7) := [((2, 3), 0), ((1, 1), 2)]
private def live : Signing.Table Nat (ZMod 7) (ZMod 7) := [((4, 4), 4), ((5, 5), 3)]
private def saved : List (Schnorr.TapeCell (ZMod 7)) := [(3, 0, 1), (1, 6, 0)]
private def remaining : List (Schnorr.TapeCell (ZMod 7)) := [(1, 5, 0), (8, 0, 20), (9, 0, 10)]
private def store (saved remaining : List (Schnorr.TapeCell (ZMod 7))) : Schnorr.ListROM.Shared.Store (ZMod 7) (ZMod 7) Nat :=
  (((2, 4), managed, live), saved, remaining)

private def run (swapped : Bool) (n : Nat) (saved remaining : List (Schnorr.TapeCell (ZMod 7))) (replies : List (Word 16)) := do
  let raw := (n, store saved remaining)
  let value : (Random.input (config swapped)).Value ← if valid : (Random.input (config swapped)).valid raw then
    some ⟨raw, valid⟩ else none
  let initial := (Random.input (config swapped)).representation.initial value
  let before := { initial with
    regs := fun r => if r = 99 then 91 else initial.regs r
    bufs := fun b => if b = 200 then #[77] else initial.bufs b
    caps := fun b => if b = 200 then 4 else initial.caps b
    tapePos := 9 }
  let result ← WordIO.run .unit RandomTape.zero 1000000
    ((Random.code (config swapped)).lower (Fresh.port (config swapped).handler.sampler.tape)) before replies
  pure (((Random.output (config swapped)).representation.encoding.decode (result.state.bufs 0).toList).map Subtype.val,
    result.trace, result.remaining, result.state.bufs 200, result.state.caps 200, result.state.regs 99,
    result.state.tapePos, (List.range 30).all (fun i => result.state.caps (i + 1) == 0),
    decide (result.time ≤ Random.timeBudget (config swapped)))

private theorem matches_original (value : (Random.input (config false)).Value) :
    Subtype.val <$> Random.source (config false) value =
      (fun answer => ((value.val.1, answer.1.val), answer.2)) <$>
        (Schnorr.ListROM.Shared.interpret
          (Schnorr.ListROM.handler (G₂ := ZMod 7) (K := Nat) (.inl (.inl value.val.1)))).run value.val.2 := by
  have same : PrivateSampler.Enumerated.sampleable (config false).sampler = FinEnum.SampleableType (ZMod 7) :=
    PrivateSampler.Enumerated.sampleable_finEnum 3 (by decide) (by decide) (by decide)
  have original := Random.source_original (G₂ := ZMod 7) (K := Nat) (config false) value
  rw [same] at original
  exact original

open Lean in
run_cmd do
  unless run false 6 saved remaining [88] ==
      some (some ((6, 6), store saved [(1, 5, 0), (9, 0, 10)]), [], [88], #[77], 4, 91, 9, true, true) do
    throwError "private replay must decode modulo the requested range, preserve full caches and consume only its family"
  unless run false 6 saved [(1, 5, 0), (8, 0, 20), (8, 0, 3)] [] ==
      some (some ((6, 6), store saved [(1, 5, 0), (8, 0, 3)]), [], [], #[77], 4, 91, 9, true, true) do
    throwError "private replay must consume only the first matching cell"
  for answer in [(0 : Word 16), 4, 7] do
    unless run false 7 saved [(1, 5, 0), (8, 0, 20)] [7, answer, 88] ==
        some (some ((7, answer.toNat), store (saved ++ [(9, 0, answer.toNat)]) [(1, 5, 0), (8, 0, 20)]),
          [.output 7, .invoke, .input 7, .input answer], [88], #[77], 4, 91, 9, true, true) do
      throwError "fresh private randomness must retain the dynamic range and fill the last saved slot"
  unless run false 0 saved [] [0, 0, 88] ==
      some (some ((0, 0), store (saved ++ [(2, 0, 0)]) []),
        [.output 0, .invoke, .input 0, .input 0], [88], #[77], 4, 91, 9, true, true) do
    throwError "singleton private random range was not encoded or decoded correctly"
  unless run false 65533 saved [] [65533, 65532, 88] ==
      some (some ((65533, 65532), store (saved ++ [(65535, 0, 65532)]) []),
        [.output 65533, .invoke, .input 65533, .input 65532], [88], #[77], 4, 91, 9, true, true) do
    throwError "maximum represented private range must execute within the same range-independent budget"
  unless run true 7 saved [(1, 5, 0)] [7, 4, 88] ==
      some (some ((7, 4), store (saved ++ [(9, 0, 4)]) [(1, 5, 0)]),
        [.output 7, .invoke, .input 7, .input 4], [88], #[77], 4, 91, 9, true, true) do
    throwError "private query lost the scalar-zero encoding while retaining the shared state"
  unless run false 7 saved [] [] == none && run false 7 saved [] [7] == none do
    throwError "private fresh query succeeded without a complete oracle reply"
  unless run false 65534 saved [] [] == none && run false 7 (saved ++ [(3, 0, 1)]) [] [7, 4] == none do
    throwError "private query admitted an overflowing family tag or a missing saved-tape reservation"
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``Schnorr.RawTape.oracle_lengths, ``Random.refines, ``Random.source_value,
      ``Random.source_original, ``Random.observe_original, ``Random.preserves_caches, ``Random.preserves_range,
      ``Random.tape_lengths, ``Random.reserved_after, ``Random.time_bound, ``Random.code_bound,
      ``Random.names, ``Random.buffers, ``Random.descriptionFits, ``Random.resources, ``matches_original] do
    for dependency in (← collectAxioms name) do
      unless dependency ∈ allowed do throwError "unexpected axiom {dependency} in {name}"

end SignaturesTest.CaliperSchnorrROMRandom
