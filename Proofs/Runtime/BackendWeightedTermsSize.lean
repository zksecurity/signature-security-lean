import Proofs.Runtime.WeightedTermsDescription
import Proofs.Runtime.BackendDataSize

/-! Native output sizes for the actual generated lists. Topic/slot encodings are
bounded only for the supplied input; neither domain needs a finite universe. -/

open PFunctor

namespace Signatures.Runtime.WeightedAGM.Terms

open Weights BackendProgram

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}

/-- A structural vector charges each coordinate and every tuple header. -/
theorem tuple_size {Atom : Type} {base : Atom → Type}
    (rep : LanguageRepresentation C base) {header : Nat} (sizes : SizeLaws Q header)
    (cell : Ty Atom) (n : Nat) (x : (tupleTy cell n).Value base)
    (width : Nat) (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hc : ∀ c, Q.size (rep.ty cell) c ≤ width) :
    Q.size (rep.ty (tupleTy cell n)) x ≤ (2 * n + 1) * width := by
  induction n with
  | zero => cases x; simpa using hu
  | succ n ih =>
      have hp := sizes.prod_le (rep.ty cell) (rep.ty (tupleTy cell n)) x
      have htail := ih x.2
      have hhead := hc x.1
      change Q.size (rep.ty (tupleTy cell (n + 1))) x ≤ _ at hp
      nlinarith

variable
  {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)

include sizes lists

theorem oopsFrom_output_size (cost : PrimitiveCosts) (d n start : Nat) (p : F) (mt : F × K)
    {Γ : List (Ty CryptoAtom)} (env : Env (cryptoBase F G₁ G₂ K M) Γ)
    (width : Nat) (hh : header ≤ width)
    (hf : ∀ x : F, Q.size (rep.ty scalar) x ≤ width)
    (hk : Q.size (rep.ty key) mt.2 ≤ width)
    (hj : ∀ j : Fin (d + 1), Q.size (rep.ty (boundedNat d)) j ≤ width) :
    Q.size (rep.ty (.list (termTy (oopsKey d))))
      ((oopsFrom d n start).denote (arithmetic F G₁ G₂ K M cost) (p, mt, env)) ≤
        (6 * n + 1) * width := by
  rw [← Expr.run_value, oopsFrom_value]
  apply (lists.size_le_length _ _ (5 * width) ?_).trans
  · simp only [List.length_ofFn]
    nlinarith
  · intro row hr
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hr
    have hp := @sizes.prod_le
    have hs := hf (p * mt.1 ^ j.val)
    have hi := hj ⟨(start + j.val) % (d + 1), Nat.mod_lt _ (Nat.zero_lt_succ d)⟩
    dsimp only [termTy, oopsKey, LanguageRepresentation.ty] at *
    grind only

theorem proximityFrom_output_size (cost : PrimitiveCosts) (ell n start : Nat)
    (ms : (proximityTupleMessage n).Value (cryptoBase F G₁ G₂ K M))
    {Γ : List (Ty CryptoAtom)} (env : Env (cryptoBase F G₁ G₂ K M) Γ)
    (width : Nat) (hh : header ≤ width)
    (hf : ∀ x : F, Q.size (rep.ty scalar) x ≤ width)
    (hk : Q.size (rep.ty key) ms.2 ≤ width)
    (hj : ∀ j : Fin (ell + 1), Q.size (rep.ty (boundedNat ell)) j ≤ width) :
    Q.size (rep.ty (.list (termTy (proximityKey ell))))
      ((proximityFrom ell n start).denote (arithmetic F G₁ G₂ K M cost) (ms, env)) ≤
        (6 * n + 1) * width := by
  rw [← Expr.run_value, proximityFrom_value]
  apply (lists.size_le_length _ _ (5 * width) ?_).trans
  · simp only [List.length_ofFn]
    nlinarith
  · intro row hr
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hr
    have hp := @sizes.prod_le
    have hs := hf (Tuple.decode n ms.1 j)
    have hi := hj ⟨(start + j.val) % (ell + 1), Nat.mod_lt _ (Nat.zero_lt_succ ell)⟩
    dsimp only [termTy, proximityKey, LanguageRepresentation.ty] at *
    grind only

theorem oops_output_size (cost : PrimitiveCosts) (d : Nat) (mt : F × K)
    (width : Nat) (hh : header ≤ width)
    (hf : ∀ x : F, Q.size (rep.ty scalar) x ≤ width)
    (hk : Q.size (rep.ty key) mt.2 ≤ width)
    (hj : ∀ j : Fin (d + 1), Q.size (rep.ty (boundedNat d)) j ≤ width) :
    Q.size (rep.ty (.list (termTy (oopsKey d))))
      ((oops d).denote (arithmetic F G₁ G₂ K M cost) (mt, ())) ≤ (6 * (d + 1) + 1) * width :=
  oopsFrom_output_size rep sizes lists cost d (d + 1) 0 1 mt (Γ := []) () width hh hf hk hj

theorem proximity_output_size (cost : PrimitiveCosts) (ell : Nat)
    (ms : (proximityTupleMessage ell).Value (cryptoBase F G₁ G₂ K M))
    (width : Nat) (hh : header ≤ width)
    (hf : ∀ x : F, Q.size (rep.ty scalar) x ≤ width)
    (hk : Q.size (rep.ty key) ms.2 ≤ width)
    (hj : ∀ j : Fin (ell + 1), Q.size (rep.ty (boundedNat ell)) j ≤ width) :
    Q.size (rep.ty (.list (termTy (proximityKey ell))))
      ((proximity ell).denote (arithmetic F G₁ G₂ K M cost) (ms, ())) ≤ (6 * (ell + 1) + 1) * width := by
  have ht := proximityFrom_output_size rep sizes lists cost ell ell 1 ms (Γ := []) () width hh hf hk hj
  have hrow : Q.size (rep.ty (termTy (proximityKey ell))) ((0, ms.2), 1) ≤ 5 * width := by
    have hp := @sizes.prod_le
    have h1 := hf 1
    have h0 := hj 0
    dsimp only [termTy, proximityKey, LanguageRepresentation.ty] at *
    grind only
  have hc := lists.cons_le (rep.ty (termTy (proximityKey ell))) ((0, ms.2), 1)
    ((proximityFrom ell ell 1 (Γ := [])).denote (arithmetic F G₁ G₂ K M cost) (ms, ()))
  change Q.size (rep.ty (.list (termTy (proximityKey ell))))
    (((0, ms.2), 1) :: ((proximityFrom ell ell 1 (Γ := [])).denote
      (arithmetic F G₁ G₂ K M cost) (ms, ()))) ≤ _
  nlinarith

end Signatures.Runtime.WeightedAGM.Terms
