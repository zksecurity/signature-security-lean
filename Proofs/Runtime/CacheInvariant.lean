import Proofs.Runtime.Cache

/-! Entry provenance for the implemented association-list cache. A lookup can
only retain the current list or prepend its requested key and returned value.
This supports message-size invariants without restricting the key universe.
-/

open OracleComp OracleSpec

namespace Signatures.Runtime

variable {Atom : Type} {base : Atom → Type} {Op Cmd : Ty Atom → Ty Atom → Type}
  {key val : Ty Atom} {I : Type} {spec : OracleSpec I}

theorem cacheHandler_list_eq (P : Primitives base Op) (H : Handler base Cmd spec)
    (eq : Op (.pair key key) .bool) (draw : Cmd .unit val)
    [DecidableEq (key.Value base)]
    (heq : ∀ x y, P.execute eq (x, y) = decide (x = y))
    (k : key.Value base) (default : val.Value base) (xs : List (key.Value base × val.Value base))
    (z : Run (val.Value base) × List (key.Value base × val.Value base))
    (hz : z ∈ support ((cacheHandler P H eq draw default k).run xs)) :
    z.2 = xs ∨ z.2 = (k, z.1.value) :: xs := by
  have hv : (z.1.value, z.2) ∈ support
      ((fun z => (z.1.value, z.2)) <$> (cacheHandler P H eq draw default k).run xs) := by
    rw [support_map]
    exact ⟨z, hz, rfl⟩
  rw [cacheHandler_erase P H eq draw heq] at hv
  split at hv
  · simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hv
    exact Or.inl hv.2
  · simp only [support_map, Set.mem_image] at hv
    obtain ⟨r, _, he⟩ := hv
    have hr := congrArg Prod.fst he
    have hs := congrArg Prod.snd he
    dsimp only at hr hs
    exact Or.inr (by simpa only [hr] using hs.symm)

theorem cacheHandler_keys (P : Primitives base Op) (H : Handler base Cmd spec)
    (eq : Op (.pair key key) .bool) (draw : Cmd .unit val)
    [DecidableEq (key.Value base)]
    (heq : ∀ x y, P.execute eq (x, y) = decide (x = y))
    (valid : key.Value base → Prop)
    (k : key.Value base) (default : val.Value base) (xs : List (key.Value base × val.Value base))
    (hk : valid k) (hx : ∀ p ∈ xs, valid p.1)
    (z : Run (val.Value base) × List (key.Value base × val.Value base))
    (hz : z ∈ support ((cacheHandler P H eq draw default k).run xs)) :
    ∀ p ∈ z.2, valid p.1 := by
  rcases cacheHandler_list_eq P H eq draw heq k default xs z hz with h | h
  · simpa only [h] using hx
  · intro p hp
    rw [h, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact hk
    · exact hx p hp

end Signatures.Runtime
