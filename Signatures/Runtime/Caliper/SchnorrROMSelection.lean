import Signatures.Runtime.Caliper.SchnorrROMSelectionVerification
import Signatures.Runtime.Caliper.SchnorrROMSelectionGuard

/-! The executed Schnorr fork-point selector. Verify the returned signature,
scan the stored LIVE entries, then check the chronological query ordinal. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.Selection
open Caliper BoundedSource
variable {w : Nat} {M F G : Type} [Zero F] [SMul F G] [Sub G]
    [DecidableEq M] [DecidableEq G]
    (config : Signing.Enumerated.Configuration w M F G) (ops : Handler.Operations config)
    (qH : Nat) (fits : qH + 1 < 2 ^ w)

def search := ((liveInput config).then (ChronologicalIndex.constructed (chronology config))).then
  (Guard.constructed config qH fits)
def rejected := Constructed.constant (input config) (result config)
  ⟨(false, 0), trivial, Nat.zero_lt_succ _⟩ config.sampler.wordFits
def source (qH : Nat) (value : Input M F G) : Bool × Nat :=
  if verified value then
    Guard.source qH (ChronologicalIndex.value ((value.1.1.1, value.1.1.2.1), value.2.1.2.2))
  else (false, 0)
def compiled := (verify config ops).checkedBranch (hw := config.sampler.wordFits)
  (search config qH fits).implementation (rejected config).implementation (by decide)
    (duplicate config) (tagged config)
theorem accepted : (compiled config ops qH fits).isSome := by
  obtain ⟨implementation, equal, _⟩ := Implementation.checkedBranch_accept
    (verify config ops) (search config qH fits).implementation (rejected config).implementation
    (by decide) (verify_buffers config ops) (search config qH fits).buffers_le (rejected config).buffers_le
    (by have := config.sampler.wordFits; have := ops.reserve; omega) (duplicate config) (tagged config)
  rw [compiled, equal]
  rfl
def implementation : Implementation .unit (input config) (result config) (source qH) :=
  (compiled config ops qH fits).get (accepted config ops qH fits)
theorem buffers : (implementation config ops qH fits).program.code.memBound ≤ max 8 (ops.slots + 3) := by
  obtain ⟨implementation, equal, bounded⟩ := Implementation.checkedBranch_accept
    (verify config ops) (search config qH fits).implementation (rejected config).implementation
    (by decide) (verify_buffers config ops) (search config qH fits).buffers_le (rejected config).buffers_le
    (by have := config.sampler.wordFits; have := ops.reserve; omega) (duplicate config) (tagged config)
  rw [show Selection.implementation config ops qH fits = implementation from
    Option.get_of_eq_some (accepted config ops qH fits) equal]
  change _ ≤ max (max 2 (max 5 ops.slots + 2) + 1) (max (max (max 4 7) 4) 2) at bounded
  exact bounded.trans (by omega)
theorem names : NamesAccounted (implementation config ops qH fits).program.code ops.slots :=
  Implementation.checkedBranch_names _ _ _ (duplicate config) (tagged config)
    (verify_names config ops) ((search config qH fits).names ops.slots) ((rejected config).names ops.slots)
    (implementation config ops qH fits) (Option.eq_some_of_isSome (accepted config ops qH fits))

variable (budget : Handler.Budget config ops)
def selectionBudget : Budget := .branch (input config).representation.encoding.words
  (verificationBudget config ops budget) (search config qH fits).budget (rejected config).budget
theorem bounded : (implementation config ops qH fits).BoundedBy
    (selectionBudget config ops qH fits budget).time (selectionBudget config ops qH fits budget).words :=
  Implementation.checkedBranch_boundedBy _ _ _ (duplicate config) (tagged config) _ _ _ _ _ _
    (verify_bounded config ops budget) (search config qH fits).bounded (rejected config).bounded
    (implementation config ops qH fits) (Option.eq_some_of_isSome (accepted config ops qH fits))

/-- The pass's typed output has exactly the selector's input bytes. -/
def realizer : Realizer .unit (ForgeryHash.output config) (result config).representation
    (fun value => ⟨source qH (represented config value).val,
      (implementation config ops qH fits).preserves _ (represented config value).property⟩) :=
  (implementation config ops qH fits).program.viewInput (ForgeryHash.output config)
    (represented config) (represented_bytes config)

end Signatures.Runtime.CaliperBackend.SchnorrROM.Selection
