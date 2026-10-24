import Proofs.Runtime.Caliper.SchnorrROMTerminalSource
import Lean

open Caliper OracleComp OracleSpec Signatures.Runtime Signatures.Runtime.CaliperBackend BoundedSource
namespace SignaturesTest.CaliperSchnorrROMTerminal
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

private abbrev Pending := (Word 16 × Word 16) × (Word 16 × Word 16)
private def pending : Representation 16 Pending :=
  (WordBinary.pair 16 (by decide)).prod (WordBinary.pair 16 (by decide)) (by decide)
private theorem room (swapped : Bool) : 8 * Terminal.width (config swapped) pending < 2 ^ 16 := by
  cases swapped <;> decide

private instance (swapped : Bool)
    (value : (Nat × ZMod 7) × Schnorr.ListROM.Shared.Store (ZMod 7) (ZMod 7) Nat) :
    Decidable ((FinalHash.rawInput (config swapped)).valid value) := by
  change Decidable ((value.1.1 < 256 ∧ True) ∧
    (((True ∧ True) ∧
      (value.2.1.2.1.length ≤ 2 ∧ ∀ entry ∈ value.2.1.2.1, (entry.1.1 < 256 ∧ True) ∧ True) ∧
      (value.2.1.2.2.length ≤ 2 ∧ ∀ entry ∈ value.2.1.2.2, (entry.1.1 < 256 ∧ True) ∧ True)) ∧
      (value.2.2.1.length ≤ 3 ∧ ∀ cell ∈ value.2.2.1, cell.1 < 65536 ∧ True ∧ cell.2.2 < 65536) ∧
      (value.2.2.2.length ≤ 3 ∧ ∀ cell ∈ value.2.2.2, cell.1 < 65536 ∧ True ∧ cell.2.2 < 65536)))
  infer_instance

private def managed : Signing.Table Nat (ZMod 7) (ZMod 7) := [((2, 3), 6), ((1, 1), 2)]
private def saved : List (Schnorr.TapeCell (ZMod 7)) := [(3, 0, 1), (8, 0, 2)]
private def remaining : List (Schnorr.TapeCell (ZMod 7)) := [(8, 0, 20), (1, 5, 0), (9, 0, 4)]
private def privateOnly : List (Schnorr.TapeCell (ZMod 7)) := [(8, 0, 20), (9, 0, 4)]
private def live : Signing.Table Nat (ZMod 7) (ZMod 7) := [((1, 1), 4)]
private def store (live : Signing.Table Nat (ZMod 7) (ZMod 7))
    (saved remaining : List (Schnorr.TapeCell (ZMod 7))) : Schnorr.ListROM.Shared.Store (ZMod 7) (ZMod 7) Nat :=
  (((2, 4), managed, live), saved, remaining)

private def run (swapped stop : Bool) (key : Nat × ZMod 7) (response : ZMod 7)
    (live : Signing.Table Nat (ZMod 7) (ZMod 7)) (saved remaining : List (Schnorr.TapeCell (ZMod 7)))
    (replies : List (Word 16)) := do
  let raw := (key, store live saved remaining)
  let value : (FinalHash.rawInput (config swapped)).Value ← if valid : (FinalHash.rawInput (config swapped)).valid raw then
    some ⟨raw, valid⟩ else none
  let forge : (ForgeryHash.forgery (config swapped)).Value :=
    ⟨(value.val.1.1, value.val.1.2, response), value.property.1.1, value.property.1.2, trivial⟩
  let stored : (config swapped).handler.store.Value := ⟨value.val.2, value.property.2⟩
  if !stop && !decide (ForgeryHash.ready (config swapped) (forge, stored)) then none else do
    let packet : Terminal.Input (config swapped) (P := Pending) :=
      ((if stop then .inr ((5, 6), (7, 8)) else .inl forge), stored)
    let initial := (Terminal.input (config swapped) pending (room swapped)).initial packet
    let before := { initial with
      regs := fun r => if r = 99 then 91 else initial.regs r
      bufs := fun b => if b = 200 then #[77] else initial.bufs b
      caps := fun b => if b = 200 then 4 else initial.caps b
      tapePos := 9 }
    let result ← WordIO.run .unit RandomTape.zero 1000000
      ((Terminal.code (config swapped) pending (room swapped)).lower (Fresh.port (config swapped).handler.sampler.tape)) before replies
    pure (((Terminal.output (config swapped) pending (room swapped)).encoding.decode (result.state.bufs 0).toList).map
        (Terminal.observed (config swapped)),
      result.trace, result.remaining, result.state.bufs 200, result.state.caps 200, result.state.regs 99,
      result.state.tapePos, (List.range 30).all (fun i => result.state.caps (i + 1) == 0),
      decide (result.time ≤ Terminal.timeBudget (config swapped) pending))

private theorem matches_original (forge : (ForgeryHash.forgery (config false)).Value)
    (stored : (config false).handler.store.Value) (valid : ForgeryHash.ready (config false) (forge, stored)) :
    Terminal.observed (config false) <$> Terminal.source (config false) (P := Pending) (.inl forge, stored) =
      (fun hashed => (some (forge.val, hashed.1), hashed.2)) <$>
        (Schnorr.ListROM.Shared.interpret (Schnorr.ListROM.finalHash (G₂ := ZMod 7) (K := Nat)
          (ForgeryHash.key (config false) forge))).run stored.val := by
  have same : PrivateSampler.Enumerated.sampleable (config false).sampler = FinEnum.SampleableType (ZMod 7) :=
    PrivateSampler.Enumerated.sampleable_finEnum 3 (by decide) (by decide) (by decide)
  have original := Terminal.source_returned (G₂ := ZMod 7) (K := Nat) (P := Pending) (config false) forge stored valid
  rw [same] at original
  exact original

open Lean in
run_cmd do
  let full : Signing.Table Nat (ZMod 7) (ZMod 7) := [((1, 1), 4), ((2, 3), 0)]
  for response in [(0 : ZMod 7), 6] do
    unless run false false (2, 3) response full saved remaining [88] ==
        some (some (some ((2, 3, response), 0), store full saved remaining), [], [88], #[77], 4, 91, 9, true, true) do
      throwError "terminal hit must retain the complete forgery, LIVE zero, managed table and tapes"
    unless run false false (2, 3) response live saved remaining [88] ==
        some (some (some ((2, 3, response), 5), store (((2, 3), 5) :: live) saved privateOnly),
          [], [88], #[77], 4, 91, 9, true, true) do
      throwError "terminal replay must retain the response scalar and insert only in LIVE"
    for answer in [(0 : Word 16), 3, 6] do
      let field : ZMod 7 := answer.toNat
      unless run false false (2, 3) response live saved privateOnly [6, answer, 88] ==
          some (some (some ((2, 3, response), field), store (((2, 3), field) :: live) (saved ++ [(1, field, 0)]) privateOnly),
            [.output 6, .invoke, .input 6, .input answer], [88], #[77], 4, 91, 9, true, true) do
        throwError "terminal fresh hash must preserve the forgery and fill the last reserved slots"
  unless run true false (2, 3) 0 live saved privateOnly [6, 0, 88] ==
      some (some (some ((2, 3, 0), 1), store (((2, 3), 1) :: live) (saved ++ [(1, 1, 0)]) privateOnly),
        [.output 6, .invoke, .input 6, .input 0], [88], #[77], 4, 91, 9, true, true) do
    throwError "terminal confused scalar zero with word zero under the swapped encoding"
  let duplicates : Signing.Table Nat (ZMod 7) (ZMod 7) := [((2, 3), 1), ((2, 3), 5)]
  unless run false false (2, 3) 4 duplicates saved remaining [] ==
      some (some (some ((2, 3, 4), 1), store duplicates saved remaining), [], [], #[77], 4, 91, 9, true, true) do
    throwError "terminal did not use the first LIVE match"
  let fullTape := saved ++ [(1, 0, 0)]
  unless run true true (3, 2) 6 full fullTape remaining [88] ==
      some (some (none, store full fullTape remaining), [], [88], #[77], 4, 91, 9, true, true) do
    throwError "cutoff must skip hashing and preserve even exhausted stores across union padding"
  unless run false false (2, 3) 4 live saved privateOnly [] == none &&
      run false false (2, 3) 4 live saved privateOnly [6] == none do
    throwError "terminal succeeded without a complete fresh oracle reply"
  unless run false false (3, 2) 4 full saved remaining [] == none &&
      run false false (2, 3) 4 live fullTape [] [6, 3] == none do
    throwError "terminal accepted an exhausted insertion or tape reservation"
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``ForgeryHash.refines, ``ForgeryHash.source_original, ``ForgeryHash.observe_original,
      ``ForgeryHash.preserves_forgery, ``ForgeryHash.preserves_config, ``ForgeryHash.preserves_managed,
      ``ForgeryHash.growth, ``ForgeryHash.reserved_ready, ``ForgeryHash.time_bound, ``ForgeryHash.code_bound,
      ``ForgeryHash.names, ``ForgeryHash.buffers, ``ForgeryHash.descriptionFits, ``ForgeryHash.resources,
      ``Terminal.refines, ``Terminal.reserved_ready, ``Terminal.source_returned, ``Terminal.source_cutoff,
      ``Terminal.preserves_config, ``Terminal.time_bound, ``Terminal.code_bound, ``Terminal.names,
      ``Terminal.buffers, ``Terminal.descriptionFits, ``Terminal.resources, ``matches_original] do
    for dependency in (← collectAxioms name) do
      unless dependency ∈ allowed do throwError "unexpected axiom {dependency} in {name}"

end SignaturesTest.CaliperSchnorrROMTerminal
