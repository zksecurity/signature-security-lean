import Proofs.Runtime.Caliper.SchnorrROMFreshGuardStep

/-! The per-cell body has uniform linear bounds in encoded tape width. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.FreshGuard
open Caliper BoundedSource SchnorrROMTape
variable {w : Nat} {F : Type} [DecidableEq F] (layout : Layouts w F)

theorem body_budget : (stepConstructed layout).budget.time ≤ 10000 * layout.width + 1000 ∧
    (stepConstructed layout).budget.words ≤ 40000 * layout.width + 10000 := by
  have entrySize := layout.entry_le
  have payloadWords : layout.payload.representation.encoding.words = layout.scalar.representation.encoding.words + 1 := rfl
  have counterWords : (Layout.counter w (2 ^ w) (width_pos layout.wordFits) le_rfl).representation.encoding.words = 1 := rfl
  have bodySize := (sizes layout).2.1
  have scalarSize := width_min layout
  have flagsWords : (flags layout).representation.encoding.words = 2 := rfl
  have stateWords : (state layout).representation.encoding.words = 3 := rfl
  have tailWords : (tail layout).representation.encoding.words = 3 + layout.scalar.representation.encoding.words := rfl
  dsimp only [stepConstructed, searching, publicStep, found, current, context, isPublic, isZero, hit, miss,
    selectedFlags, pendingFlags, yes, equal, scalarEquality, scalar, answer, cell, tag, count, natural,
    arguments, decrement, combine, Constructed.castFunction, Constructed.branch, Constructed.then,
    Constructed.pair, Constructed.first, Constructed.second, Constructed.constant, Constructed.equal,
    Constructed.subtract, Budget.branch, Budget.seq, Budget.pair, Budget.storage]
  simp only [flagsWords, stateWords, tailWords, payloadWords, counterWords, Layout.prod_words, Layouts.counter_words, Layouts.boolean_words]
  exact ⟨by omega, by omega⟩

end Signatures.Runtime.CaliperBackend.SchnorrROM.FreshGuard
