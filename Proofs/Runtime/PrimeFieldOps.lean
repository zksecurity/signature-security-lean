import Proofs.Runtime.PrimeFieldCircuit

/-! The remaining scalar primitives: constants, modular addition, negation, and
equality. Together with PrimeFieldCircuit these cover every scalar CryptoOp.
Inputs are canonical field encodings; the word-width obligation is explicit. -/

namespace Signatures.Runtime.PrimeFieldCircuit

open Std.Sat Std.Tactic.BVDecide BVExpr.bitblast

variable {A : Type} [Hashable A] [DecidableEq A] {w : Nat}

def zero (aig : AIG A) : Built aig w :=
  ⟨⟨aig, blastConst aig (BitVec.ofNat w 0)⟩, AIG.IsPrefix.rfl⟩

def one (aig : AIG A) : Built aig w :=
  ⟨⟨aig, blastConst aig (BitVec.ofNat w 1)⟩, AIG.IsPrefix.rfl⟩

theorem zero_size (aig : AIG A) : (zero (w := w) aig).result.aig.decls.size = aig.decls.size := rfl
theorem one_size (aig : AIG A) : (one (w := w) aig).result.aig.decls.size = aig.decls.size := rfl

def add (aig : AIG A) (input : AIG.BinaryRefVec aig w) (p : Nat) : Built aig w :=
  let sum := blastAdd aig input
  let h₁ := AIG.LawfulVecOperator.isPrefix_aig (f := blastAdd) aig input
  let reduced := blastUmod sum.aig ⟨sum.vec, blastConst sum.aig (BitVec.ofNat w p)⟩
  let h₂ := AIG.LawfulVecOperator.isPrefix_aig (f := blastUmod) sum.aig
    ⟨sum.vec, blastConst sum.aig (BitVec.ofNat w p)⟩
  ⟨reduced, ⟨h₁.size_le.trans h₂.size_le,
    fun i hi => (h₂.idx_eq i (hi.trans_le h₁.size_le)).trans (h₁.idx_eq i hi)⟩⟩

theorem add_size (aig : AIG A) (input : AIG.BinaryRefVec aig w) (p : Nat) :
    (add aig input p).result.aig.decls.size ≤ aig.decls.size + 36 * w * w + 19 * w := by
  unfold add
  dsimp only
  refine (BitCircuit.mod_size _ _).trans ?_
  have := BitCircuit.add_size aig input
  omega

theorem add_bits (aig : AIG A) (input : AIG.BinaryRefVec aig w) (p : Nat)
    (assign : A → Bool) (x y : BitVec w)
    (hx : Represents assign aig input.lhs x) (hy : Represents assign aig input.rhs y) :
    Represents assign (add aig input p).result.aig (add aig input p).result.vec
      ((x + y) % BitVec.ofNat w p) := by
  apply denote_blastUmod
  · exact denote_blastAdd aig x y assign input hx hy
  · exact denote_blastConst _ _ _

def negate (aig : AIG A) (input : AIG.RefVec aig w) (p : Nat) : Built aig w :=
  subtract aig ⟨blastConst aig (BitVec.ofNat w 0), input⟩ p

theorem negate_size (aig : AIG A) (input : AIG.RefVec aig w) (p : Nat) :
    (negate aig input p).result.aig.decls.size ≤ aig.decls.size + 36 * w * w + 43 * w :=
  subtract_size aig _ p

variable {p : Nat} [Fact p.Prime]

theorem zero_correct (aig : AIG A) (assign : A → Bool) :
    Represents assign (zero aig).result.aig (zero aig).result.vec
      (BitVec.ofNat w (0 : ZMod p).val) := by
  simpa only [ZMod.val_zero, zero, Represents] using denote_blastConst aig (BitVec.ofNat w 0) assign

theorem one_correct (aig : AIG A) (assign : A → Bool) :
    Represents assign (one aig).result.aig (one aig).result.vec
      (BitVec.ofNat w (1 : ZMod p).val) := by
  simpa only [ZMod.val_one, one, Represents] using denote_blastConst aig (BitVec.ofNat w 1) assign

theorem add_word (hfit : p * p ≤ 2 ^ w) (x y : ZMod p) :
    ((BitVec.ofNat w x.val + BitVec.ofNat w y.val) % BitVec.ofNat w p) =
      BitVec.ofNat w (x + y).val := by
  have hp₂ := (Fact.out : p.Prime).two_le
  have hp : p < 2 ^ w := by nlinarith
  have hx := x.val_lt
  have hy := y.val_lt
  have hsum : x.val + y.val < 2 ^ w := by nlinarith
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_umod, BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (hx.trans hp), Nat.mod_eq_of_lt (hy.trans hp),
    Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt hsum,
    Nat.mod_eq_of_lt ((x + y).val_lt.trans hp)]
  exact (ZMod.val_add x y).symm

theorem add_correct (hfit : p * p ≤ 2 ^ w) (aig : AIG A)
    (input : AIG.BinaryRefVec aig w) (assign : A → Bool) (x y : ZMod p)
    (hx : Represents assign aig input.lhs (BitVec.ofNat w x.val))
    (hy : Represents assign aig input.rhs (BitVec.ofNat w y.val)) :
    Represents assign (add aig input p).result.aig (add aig input p).result.vec
      (BitVec.ofNat w (x + y).val) := by
  rw [← add_word hfit]
  exact add_bits aig input p assign _ _ hx hy

theorem negate_correct (hfit : p * p ≤ 2 ^ w) (aig : AIG A)
    (input : AIG.RefVec aig w) (assign : A → Bool) (x : ZMod p)
    (hx : Represents assign aig input (BitVec.ofNat w x.val)) :
    Represents assign (negate aig input p).result.aig (negate aig input p).result.vec
      (BitVec.ofNat w (-x).val) := by
  simpa only [negate, zero_sub] using subtract_correct hfit aig
    ⟨blastConst aig (BitVec.ofNat w 0), input⟩ assign 0 x (zero_correct aig assign) hx

/-- Canonical residue encodings do not identify distinct field elements. -/
theorem encoding_injective (hp : p ≤ 2 ^ w) :
    Function.Injective (fun x : ZMod p => BitVec.ofNat w x.val) := by
  intro x y h
  apply ZMod.val_injective p
  have hv := congrArg BitVec.toNat h
  simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (x.val_lt.trans_le hp),
    Nat.mod_eq_of_lt (y.val_lt.trans_le hp)] using hv

theorem eq_correct (hp : p ≤ 2 ^ w) (aig : AIG A) (input : AIG.BinaryRefVec aig w)
    (assign : A → Bool) (x y : ZMod p)
    (hx : Represents assign aig input.lhs (BitVec.ofNat w x.val))
    (hy : Represents assign aig input.rhs (BitVec.ofNat w y.val)) :
    AIG.denote assign (BVPred.mkEq aig input) = decide (x = y) := by
  rw [BVPred.mkEq_denote_eq aig input assign _ _ hx hy]
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  exact (encoding_injective hp).eq_iff

end Signatures.Runtime.PrimeFieldCircuit
