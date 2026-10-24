import Proofs.Runtime.Caliper.CoronCache
import Proofs.Runtime.CoronPairedCache
import Lean

/-! Execute Coron's paired cache on empty, partially filled and full tables.
Hits consume no randomness; misses preserve scalar/coin order and the caller's
private state. The adaptive source bridge and complete certificate are audited. -/
namespace SignaturesTest.CaliperCoronCache
open Caliper OracleComp OracleSpec Signatures.Runtime Signatures.Runtime.CaliperBackend BoundedSource

private def port := UniformQuery.port (w := 8) 255 (by decide) (by decide)
private def draw := UniformSampling.code (w := 8) 255 (by decide) (by decide) (3 : Fin 256)
private def layout : CacheLayout 8 Nat (Fin 4) where
  key := Layout.counter 8 256 (by decide) (by decide)
  value := UniformSampling.output 255 (by decide) (by decide) (3 : Fin 256)
  capacityPred := 1
  wordFits := by decide
  countFits := by decide
  storageFits := by decide
private def paired := layout.coinValues 255 (by decide) (1 : Fin 256) (by decide)
private def program := CoronCache.code layout 255 (by decide) (1 : Fin 256) (by decide) draw

private theorem within : Interactive.Within port paired.input (CacheRead.output paired)
    (CoronCache.codeBudget layout 255 (by decide) (1 : Fin 256) (by decide) 125)
    (CoronCache.memoryBudget layout 255 (by decide) (1 : Fin 256) (by decide) 26 125 3)
    (CoronCache.timeBudget layout 255 (by decide) (1 : Fin 256) (by decide) 26)
    (fun input => ((BLS.LazyAGM.Reduction.privateListOracle (M := Nat) (R := Fin 4 × Fin 2))
      (.inr input.val.1)).run input.val.2.2.1) :=
  CoronCache.within layout 255 (by decide) (1 : Fin 256) (by decide)
    (UniformSampling.refines 255 (by decide) (by decide) (3 : Fin 256))
    (UniformSampling.uniform 255 (by decide) (by decide) (3 : Fin 256))
    (UniformSampling.time_bound 255 (by decide) (by decide) (3 : Fin 256))
    (UniformSampling.code_words 255 (by decide) (by decide) (3 : Fin 256))
    (UniformSampling.names 255 (by decide) (by decide) (3 : Fin 256))
    (UniformSampling.descriptionFits 255 (by decide) (by decide) (3 : Fin 256)) (by decide)

private theorem valid_iff (key : Nat) (fallback : Fin 4 × Fin 2) (entries : List (Nat × (Fin 4 × Fin 2))) :
    paired.input.valid (key, fallback, entries, ()) ↔
      (key < 256 ∧ entries.length ≤ 2 ∧ ∀ entry ∈ entries, entry.1 < 256) ∧
        ((lookupValue key fallback entries).1 = false → entries.length ≤ 1) := by
  change ((key < 256 ∧ (True ∧ True) ∧
    (entries.length ≤ 2 ∧ ∀ entry ∈ entries, entry.1 < 256 ∧ (True ∧ True)) ∧ True) ∧
    ((lookupValue key fallback entries).1 = false → entries.length ≤ 1)) ↔ _
  simp only [true_and, and_true]

private def fullHit : paired.input.Value :=
  ⟨(2, (1, 0), [(1, (3, 0)), (2, (0, 1))], ()), by rw [valid_iff]; decide +kernel⟩
private def miss : paired.input.Value :=
  ⟨(2, (1, 1), [(1, (3, 1))], ()), by rw [valid_iff]; decide +kernel⟩
private def empty : paired.input.Value :=
  ⟨(2, (1, 1), [], ()), by rw [valid_iff]; decide +kernel⟩
private def shadowed : paired.input.Value :=
  ⟨(2, (1, 1), [(2, (0, 1)), (2, (3, 0))], ()), by rw [valid_iff]; decide +kernel⟩

private def execute (value : paired.input.Value) (replies : List (Word 8)) := do
  let initial := paired.input.representation.initial value
  let before := { initial with
    regs := fun register => if register = 200 then 99 else initial.regs register
    bufs := fun buffer => if buffer = 200 then #[77] else initial.bufs buffer
    caps := fun buffer => if buffer = 200 then 3 else initial.caps buffer
    tapePos := 7 }
  let result ← WordIO.run .unit RandomTape.zero 50000 (program.lower port) before replies
  pure (result.state.bufs 0, result.trace, result.remaining,
    result.state.bufs 200, result.state.caps 200, result.state.regs 200, result.state.tapePos,
    decide (result.time ≤ CoronCache.timeBudget layout 255 (by decide) (1 : Fin 256) (by decide) 26))

-- A full table is admissible for a hit, but cannot silently discard a miss.
example : ¬paired.input.valid (3, (1, 1), [(1, (3, 0)), (2, (0, 1))], ()) := by
  rw [valid_iff]; decide +kernel

-- Both components use the first binding, including a stored zero scalar.
example : Coron.Paired.scalars [(2, ((0 : Fin 4), (1 : Fin 2))), (2, (3, 0))] 2 = some 0 := rfl
example : Coron.Paired.coins [(2, ((0 : Fin 4), (1 : Fin 2))), (2, (3, 0))] 2 = some 1 := rfl

open Lean in
run_cmd do
  unless execute fullHit [42] == some (#[0, 1, 2, 1, 3, 0, 2, 0, 1], [], [42], #[77], 3, 99, 7, true) do
    throwError "full cache hit changed its entry, sampled, or disturbed private state"
  unless execute shadowed [] == some (#[0, 1, 2, 2, 0, 1, 2, 3, 0], [], [], #[77], 3, 99, 7, true) do
    throwError "paired cache did not preserve the first shadowing binding"
  unless execute miss [3, 2, 1, 0, 42] == some (#[2, 0, 2, 2, 2, 0, 1, 3, 1],
      [.output 3, .invoke, .input 3, .input 2, .output 1, .invoke, .input 1, .input 0],
      [42], #[77], 3, 99, 7, true) do
    throwError "cache miss lost an entry or changed scalar/coin query order"
  unless execute empty [3, 2, 1, 0] == some (#[2, 0, 1, 2, 2, 0, 0, 0, 0],
      [.output 3, .invoke, .input 3, .input 2, .output 1, .invoke, .input 1, .input 0],
      [], #[77], 3, 99, 7, true) do
    throwError "empty cache did not insert its sampled scalar/coin pair"
  unless (execute miss [3, 2]).isNone do
    throwError "cache miss succeeded without receiving its coin reply"
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``Coron.Paired.scalars_cons, ``Coron.Paired.coins_cons,
      ``Coron.Paired.reply_native, ``Coron.Paired.oracle_native, ``Coron.Paired.simulation_native,
      ``Coron.Paired.reduction_native, ``Coron.Paired.reduction_original, ``Coron.Paired.simulation_growth,
      ``CoronCache.refines, ``CoronCache.time_bound, ``CoronCache.code_words, ``CoronCache.names,
      ``CoronCache.descriptionFits, ``CoronCache.source_eq, ``CoronCache.within, ``within] do
    for dependency in (← collectAxioms name) do
      unless dependency ∈ allowed do throwError "unexpected axiom {dependency} in {name}"

end SignaturesTest.CaliperCoronCache
