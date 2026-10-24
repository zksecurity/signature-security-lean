import Proofs.Runtime.Caliper.SchnorrROMEnumeratedBounds

/-! Instantiate the concrete caller with VCVio's existing FinEnum sampler.
The equality is of query programs, including the finite range and its mapping,
so callers do not supply a sampler-equivalence or termination assumption. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROMTape.PrivateSampler.Enumerated
open Caliper BoundedSource OracleComp OracleSpec

def Parameters.ofFinEnum (w : Nat) (F : Type) [FinEnum F] [Nonempty F] (capacity : Nat)
    (wordFits : 16 < 2 ^ w) (rangeFits : FinEnum.card F + 1 < 2 ^ w)
    (storageFits : 16 * (4 + (capacity + 2) * 3) < 2 ^ w) : Parameters w F where
  bound := FinEnum.card F - 1
  index := (FinEnum.equiv (α := F)).trans (finCongr (Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (FinEnum.card_ne_zero (α := F)))).symm)
  capacity := capacity
  wordFits := wordFits
  rangeFits := by have := FinEnum.card_ne_zero (α := F); omega
  storageFits := storageFits

theorem fin_uniform (n : Nat) [NeZero n] : ($ᵗ (Fin n) : ProbComp (Fin n)) =
    (finCongr (Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)))) <$>
      (unifSpec.query (n - 1) : ProbComp (Fin (n - 1 + 1))) := by
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n => rfl

variable {w : Nat} {F : Type} [FinEnum F] [Nonempty F] (capacity : Nat)
    (wordFits : 16 < 2 ^ w) (rangeFits : FinEnum.card F + 1 < 2 ^ w)
    (storageFits : 16 * (4 + (capacity + 2) * 3) < 2 ^ w)

theorem samples_finEnum
    (input : (tape (Parameters.ofFinEnum w F capacity wordFits rangeFits storageFits)).unit.Value) :
    Subtype.val <$> original (layout (Parameters.ofFinEnum w F capacity wordFits rangeFits storageFits))
      (caller (Parameters.ofFinEnum w F capacity wordFits rangeFits storageFits)) 1
      (terminates (Parameters.ofFinEnum w F capacity wordFits rangeFits storageFits)) input = ($ᵗ F : ProbComp F) := by
  rw [original_scalar]
  let : NeZero (FinEnum.card F) := ⟨FinEnum.card_ne_zero (α := F)⟩
  change _ = (FinEnum.equiv (α := F)).symm <$> ($ᵗ (Fin (FinEnum.card F)) : ProbComp (Fin (FinEnum.card F)))
  rw [fin_uniform]
  simp only [Functor.map_map]
  rfl

omit [FinEnum F] [Nonempty F] in
private theorem sampleable_ext {first second : SampleableType F} (equal : first.selectElem = second.selectElem) : first = second := by
  cases first
  cases second
  cases equal
  rfl

theorem sampleable_finEnum : sampleable (Parameters.ofFinEnum w F capacity wordFits rangeFits storageFits) = FinEnum.SampleableType F := by
  apply sampleable_ext
  exact
    (samples (Parameters.ofFinEnum w F capacity wordFits rangeFits storageFits) ⟨(), trivial⟩).symm.trans
      (samples_finEnum capacity wordFits rangeFits storageFits ⟨(), trivial⟩)

end Signatures.Runtime.CaliperBackend.SchnorrROMTape.PrivateSampler.Enumerated
