import Proofs.Runtime.Caliper.CacheBounds
import Lean

open Caliper Signatures.Runtime Signatures.Runtime.CaliperBackend
open Signatures.Runtime.CaliperBackend.BoundedSource

namespace SignaturesTest.CaliperCache

private def base (_ : Unit) : Type := Word 8
private inductive Op : Ty Unit → Ty Unit → Type
  | equal : Op (.pair .nat .nat) .bool
private def primitives : Primitives base Op where
  execute instruction := match instruction with | .equal => fun value => decide (value.1 = value.2)
  cost _ _ := 1
private def comparison : Expr Op [.nat, .nat] .bool := .op .equal (.pair (.var .here) (.var (.there .here)))
private theorem comparison_correct (left right : Nat) :
    comparison.denote primitives (left, right, ()) = decide (left = right) := rfl

private def counter := Layout.counter 8 256 (by decide) (by decide)
private def layout : CacheLayout 8 Nat Nat where
  key := counter
  value := counter
  capacityPred := 1
  wordFits := by decide
  countFits := by decide
  storageFits := by decide

private def program := EncodedCache.implementation (base := base) (key := .nat) (val := .nat)
  layout primitives comparison comparison_correct

private theorem time_eq : EncodedCache.timeBudget (base := base) (key := .nat) (val := .nat) layout = 12477 := by decide +kernel
private theorem code_eq : EncodedCache.codeBudget (base := base) (key := .nat) (val := .nat) layout = 45829 := by decide +kernel

private theorem bounded : program.BoundedBy 12477 45829 := by
  rw [← time_eq, ← code_eq]
  exact EncodedCache.bounded (base := base) (key := .nat) (val := .nat) layout primitives comparison comparison_correct

example : program.program.code.memBound ≤ 8 := by
  have same : program = EncodedCache.implementation (base := base) (key := .nat) (val := .nat)
      layout primitives comparison comparison_correct := rfl
  exact (congrArg (fun p => p.program.code.memBound) same).le.trans
    (EncodedCache.buffers (base := base) (key := .nat) (val := .nat) layout primitives comparison comparison_correct)

private def observe (value : layout.input.Value) := do
  let initial := layout.input.representation.initial value
  let before := { initial with
    bufs := fun buffer => if buffer = 200 then #[77] else initial.bufs buffer
    caps := fun buffer => if buffer = 200 then 1 else initial.caps buffer }
  let (state, _, _, _) ← Caliper.run .unit RandomTape.zero 30000 program.program.code before
  pure (state.bufs 0, state.bufs 200)

private theorem valid_iff (key value : Nat) (entries : List (Nat × Nat)) :
    layout.input.valid (key, value, entries, ()) ↔
      (key < 256 ∧ value < 256 ∧ entries.length ≤ 2 ∧ ∀ entry ∈ entries, entry.1 < 256 ∧ entry.2 < 256) ∧
      ((lookupValue key value entries).1 = false → entries.length ≤ 1) := by
  change ((key < 256 ∧ value < 256 ∧ (entries.length ≤ 2 ∧ ∀ entry ∈ entries, entry.1 < 256 ∧ entry.2 < 256) ∧ True) ∧
    ((lookupValue key value entries).1 = false → entries.length ≤ 1)) ↔ _
  tauto

private def fullHit : layout.input.Value := ⟨(2, 9, [(1, 7), (2, 0)], ()), by rw [valid_iff]; decide +kernel⟩
private def miss : layout.input.Value := ⟨(2, 9, [(1, 7)], ()), by rw [valid_iff]; decide +kernel⟩
private def empty : layout.input.Value := ⟨(2, 9, [], ()), by rw [valid_iff]; decide +kernel⟩
private def duplicateHit : layout.input.Value := ⟨(2, 9, [(2, 7), (2, 0)], ()), by rw [valid_iff]; decide +kernel⟩

-- Full hits preserve every entry, including cached zero and duplicate-key order.
example : observe fullHit = some (#[2, 1, 7, 2, 0], #[77]) := by decide +kernel
example : observe duplicateHit = some (#[2, 2, 7, 2, 0], #[77]) := by decide +kernel
-- A miss uses a free slot while preserving the same five-word table capacity.
example : observe miss = some (#[2, 2, 9, 1, 7], #[77]) := by decide +kernel
example : observe empty = some (#[1, 2, 9, 0, 0], #[77]) := by decide +kernel

-- Overflowing misses and invalid component values are outside the proved domain.
example : ¬layout.input.valid (3, 9, [(1, 7), (2, 0)], ()) := by rw [valid_iff]; decide +kernel
example : ¬layout.input.valid (256, 9, [], ()) := by rw [valid_iff]; decide +kernel

example (value : layout.input.Value) :
    ((cacheProgram (val := .nat) comparison).denote primitives value.val).length ≤ 2 :=
  ((program.preserves value.val value.property).1)

-- A zero-word entry still has a stored length header and an explicit count bound.
private def zeroLayout : CacheLayout 8 Unit Unit where
  key := DataImplementation.unitLayout 8
  value := DataImplementation.unitLayout 8
  capacityPred := 0
  wordFits := by decide
  countFits := by decide
  storageFits := by decide
private def zeroComparison : Expr Op [.unit, .unit] .bool := .bool true
private theorem zero_correct (left right : Unit) :
    zeroComparison.denote primitives (left, right, ()) = decide (left = right) := by cases left; cases right; rfl
private def zeroProgram := EncodedCache.implementation (base := base) (key := .unit) (val := .unit)
  zeroLayout primitives zeroComparison zero_correct
private def zeroEmpty : zeroLayout.input.Value := ⟨((), (), [], ()), by
  change (True ∧ True ∧ (0 ≤ 1 ∧ ∀ entry ∈ ([] : List (Unit × Unit)), True ∧ True) ∧ True) ∧ (false = false → 0 ≤ 0)
  simp⟩
example : (Caliper.run .unit RandomTape.zero 10000 zeroProgram.program.code
    (zeroLayout.input.representation.initial zeroEmpty)).map (fun result => result.1.bufs 0) = some #[1] := by decide +kernel

open Lean in
run_cmd do
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``Encoding.restrict, ``Layout.restrict, ``Implementation.restrictInput, ``Implementation.restrictOutput,
      ``Encoding.boundedList_take, ``ListData.narrow, ``ListData.narrow_boundedBy, ``ListData.fixedCons,
      ``ListData.fixedCons_boundedBy, ``ListData.fixedCons_buffers, ``ListData.fixedCons_names,
      ``GuardedBranch.selector, ``GuardedBranch.implementation, ``GuardedBranch.implementation_boundedBy,
      ``GuardedBranch.implementation_buffers, ``GuardedBranch.implementation_names,
      ``CacheFinish.implementation, ``CacheFinish.bounded, ``CacheFinish.buffers, ``CacheFinish.names,
      ``EncodedCache.implementation, ``EncodedCache.bounded, ``EncodedCache.buffers, ``EncodedCache.names,
      ``EncodedCache.staticMemory, ``EncodedCache.memoryBound, ``comparison_correct, ``zero_correct, ``bounded] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"

end SignaturesTest.CaliperCache
