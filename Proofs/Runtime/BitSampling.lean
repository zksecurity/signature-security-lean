import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Logic.Equiv.Sum

/-! A boundary on refining ideal finite uniform samplers to bounded fair randomness.
A total deterministic function of k fair bits is uniform only when all output
fibers have the same size. Adaptive samplers with at most k flips can be padded
to such a function; this file proves the finite counting obstruction, not that
padding transformation or a rejection-sampling implementation. -/

namespace Signatures.Runtime.BitSampling

/-- Equal-sized fibers are exact uniformity for a deterministic map of uniform inputs. -/
def Balanced {X Y : Type} [Fintype X] [DecidableEq Y] (f : X → Y) : Prop :=
  ∃ n : Nat, ∀ y, Fintype.card {x // f x = y} = n

theorem card_dvd_of_balanced {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq Y]
    (f : X → Y) (h : Balanced f) : Fintype.card Y ∣ Fintype.card X := by
  obtain ⟨n, hn⟩ := h
  refine ⟨n, ?_⟩
  have he := Fintype.card_congr (Equiv.sigmaFiberEquiv f)
  simpa only [Fintype.card_sigma, hn, Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul] using he.symm

/-- An odd prime number of outputs cannot be sampled exactly using a fixed fair-bit tape. -/
theorem not_balanced_prime (p bits : Nat) (hp : p.Prime) (hodd : p ≠ 2)
    (f : (Fin bits → Bool) → Fin p) : ¬ Balanced f := by
  intro h
  have hd : p ∣ 2 ^ bits := by simpa using card_dvd_of_balanced f h
  have := hp.dvd_of_dvd_pow hd
  exact hodd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)

end Signatures.Runtime.BitSampling
