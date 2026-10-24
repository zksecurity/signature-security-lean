import Proofs.Runtime.Caliper.SchnorrROMSelectionLayout

/-! An executed query-index guard. Missing entries and ordinals outside the
hash-query allowance normalize to `(false, 0)`, exactly as the source selector. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.Selection.Guard
open Caliper BoundedSource
variable {w : Nat} {M F G : Type} (config : Signing.Enumerated.Configuration w M F G)
def index := (chronology config).counter ⟨config.capacityPred + 1, Nat.lt_succ_self _⟩
def limit := Layout.counter w (2 ^ w) (width_pos config.sampler.wordFits) le_rfl
def flag := Constructed.first (boolean config) (index config) config.sampler.wordFits (result config).representation.fits
def ordinal := Constructed.second (boolean config) (index config) config.sampler.wordFits (result config).representation.fits
def allowance (qH : Nat) (fits : qH + 1 < 2 ^ w) := Constructed.constant (result config) (limit config) ⟨qH + 1, fits⟩ config.sampler.wordFits
def arguments (qH : Nat) (fits : qH + 1 < 2 ^ w) : Constructed (result config)
    (Natural.pair (config.capacityPred + 2) (2 ^ w) config.sampler.wordFits (Nat.succ_le_iff.mpr config.countFits) le_rfl)
    (fun value => (value.2, qH + 1)) :=
  (ordinal config).pair (allowance config qH fits) config.sampler.wordFits
    (by change 2 < _; have := config.sampler.wordFits; omega) (by change 2 < _; have := config.sampler.wordFits; omega)
    (by change (1 + 1) + (1 + 1) < _; have := config.sampler.wordFits; omega)
    (by change 1 + (1 + 1) < _; have := config.sampler.wordFits; omega)
    (by change 1 + 1 < _; have := config.sampler.wordFits; omega)
def less : Constructed
    (Natural.pair (config.capacityPred + 2) (2 ^ w) config.sampler.wordFits (Nat.succ_le_iff.mpr config.countFits) le_rfl)
    (boolean config) (fun value => decide (value.1 < value.2)) where
  implementation := Natural.less .unit _ _ _ _ _
  budget := ⟨6, 27⟩
  bounded := ⟨fun _ => le_rfl, (WordBinary.descriptionWords_eq .ult).le⟩
  buffers := 1
  buffers_le := le_rfl
  names slots := ⟨by change 3 ≤ slots + 27; omega, by change 1 ≤ slots + 27; omega⟩
def test (qH : Nat) (fits : qH + 1 < 2 ^ w) := (arguments config qH fits).then (less config)
def rejected := Constructed.constant (result config) (result config) ⟨(false, 0), trivial, by change 0 < config.capacityPred + 1 + 1; omega⟩
  config.sampler.wordFits
def accepted := Constructed.identity (result config) (width_pos config.sampler.wordFits)
def checked (qH : Nat) (fits : qH + 1 < 2 ^ w) := Constructed.branch config.sampler.wordFits (test config qH fits) (accepted config) (rejected config)
  (by change max 3 1 < _; have := config.sampler.wordFits; omega)
  (by change (1 + 1) + (1 + 1) < _; have := config.sampler.wordFits; omega)
  (by change 1 + (1 + 1) < _; have := config.sampler.wordFits; omega)
def source (qH : Nat) (value : Bool × Nat) := if value.1 && decide (value.2 < qH + 1) then value else (false, 0)
def constructed (qH : Nat) (fits : qH + 1 < 2 ^ w) : Constructed (result config) (result config) (source qH) :=
  (Constructed.branch config.sampler.wordFits (flag config) (checked config qH fits) (rejected config)
    (by change 2 < _; have := config.sampler.wordFits; omega)
    (by change (1 + 1) + (1 + 1) < _; have := config.sampler.wordFits; omega)
    (by change 1 + (1 + 1) < _; have := config.sampler.wordFits; omega)).castFunction (by
      funext value
      rcases value with ⟨flag, ordinal⟩
      cases flag <;> simp only [Function.comp_apply, id_eq, source, Bool.false_and, Bool.true_and, Bool.false_eq_true, ↓reduceIte])
theorem buffers (qH : Nat) (fits : qH + 1 < 2 ^ w) : (constructed config qH fits).buffers = 4 := rfl
theorem budget (qH : Nat) (fits : qH + 1 < 2 ^ w) : (constructed config qH fits).budget.time ≤ 1000 ∧ (constructed config qH fits).budget.words ≤ 4000 := by
  dsimp only [constructed, Constructed.castFunction, Constructed.branch, flag, checked, test,
    arguments, accepted, rejected, ordinal, allowance, less, Constructed.then, Constructed.first,
    Constructed.second, Constructed.constant, Constructed.identity, Constructed.pair,
    Budget.branch, Budget.pair, Budget.storage, Budget.seq, Budget.identity]
  have flagSize : (boolean config).representation.encoding.words = 1 := rfl
  have indexSize : (index config).representation.encoding.words = 1 := rfl
  have limitSize : (limit config).representation.encoding.words = 1 := rfl
  have resultSize : (result config).representation.encoding.words = 2 := rfl
  have pairedSize : ((boolean config).prod (index config) (result config).representation.fits).representation.encoding.words = 2 := rfl
  simp only [flagSize, indexSize, limitSize, resultSize, pairedSize]
  decide

end Signatures.Runtime.CaliperBackend.SchnorrROM.Selection.Guard
