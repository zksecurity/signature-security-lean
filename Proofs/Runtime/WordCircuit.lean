import Proofs.Runtime.PrimeFieldCircuit

/-! Natural-number and bounded-integer operations on binary encodings.
Natural addition needs a proved no-overflow condition; subtraction saturates at
zero, unlike ordinary bit-vector subtraction. No unbounded Nat operation is
silently treated as a fixed-width word operation. -/

namespace Signatures.Runtime.WordCircuit

open Std.Sat Std.Tactic.BVDecide BVExpr.bitblast
open PrimeFieldCircuit (Represents)

variable {A : Type} [Hashable A] [DecidableEq A] {w : Nat}

/-- Decode all bits, including leading zeros; the range condition prevents truncation. -/
theorem exponent_testBits (v n : Nat) (h : n < 2 ^ v) :
    PrimeFieldCircuit.exponent (List.ofFn (fun i : Fin v => n.testBit i)) = n := by
  induction v generalizing n with
  | zero =>
    have hn : n = 0 := by simpa using h
    simp [hn, PrimeFieldCircuit.exponent]
  | succ v ih =>
    rw [List.ofFn_succ]
    simp only [Fin.val_zero, Fin.val_succ, Nat.testBit_succ, PrimeFieldCircuit.exponent]
    rw [ih (n / 2) (by rw [Nat.pow_succ] at h; omega)]
    have hbit := Nat.toNat_testBit n 0
    simp only [Nat.pow_zero, Nat.div_one] at hbit
    omega

theorem exponent_word (x : BitVec w) :
    PrimeFieldCircuit.exponent (List.ofFn (fun i : Fin w => x.getLsbD i)) = x.toNat :=
  exponent_testBits w x.toNat x.isLt

/-- A natural encoding includes the range invariant, not just equality of low bits. -/
def RepresentsNat (assign : A → Bool) (aig : AIG A) (refs : AIG.RefVec aig w) (n : Nat) : Prop :=
  n < 2 ^ w ∧ Represents assign aig refs (BitVec.ofNat w n)

theorem add_correct (aig : AIG A) (input : AIG.BinaryRefVec aig w)
    (assign : A → Bool) (x y : Nat) (hxy : x + y < 2 ^ w)
    (hx : Represents assign aig input.lhs (BitVec.ofNat w x))
    (hy : Represents assign aig input.rhs (BitVec.ofNat w y)) :
    RepresentsNat assign (blastAdd aig input).aig (blastAdd aig input).vec (x + y) := by
  refine ⟨hxy, ?_⟩
  simpa only [Represents, BitVec.ofNat_add] using denote_blastAdd aig _ _ assign input hx hy

/-- The result's decoding is the natural sum, not its residue modulo the word size. -/
theorem add_value (x y : Nat) (hxy : x + y < 2 ^ w) :
    (BitVec.ofNat w (x + y)).toNat = x + y := by
  exact Nat.mod_eq_of_lt hxy

def subtract (aig : AIG A) (input : AIG.BinaryRefVec aig w) : AIG.RefVecEntry A w :=
  let cmp := BVPred.mkUlt aig input
  let hc := AIG.LawfulOperator.le_size (f := BVPred.mkUlt) aig input
  let sub := blastSub cmp.aig (input.cast hc)
  let hs := AIG.LawfulVecOperator.le_size (f := blastSub) cmp.aig (input.cast hc)
  AIG.RefVec.ite sub.aig ⟨cmp.ref.cast hs, blastConst sub.aig (BitVec.ofNat w 0), sub.vec⟩

theorem subtract_size (aig : AIG A) (input : AIG.BinaryRefVec aig w) :
    (subtract aig input).aig.decls.size ≤ aig.decls.size + 33 * w := by
  unfold subtract
  refine (BitCircuit.ite_size _ _).trans ?_
  refine (Nat.add_le_add_right (BitCircuit.sub_size _ _) _).trans ?_
  have := BitCircuit.ult_size aig input
  omega

theorem subtract_bits (aig : AIG A) (input : AIG.BinaryRefVec aig w)
    (assign : A → Bool) (x y : BitVec w)
    (hx : Represents assign aig input.lhs x) (hy : Represents assign aig input.rhs y) :
    Represents assign (subtract aig input).aig (subtract aig input).vec
      (BitVec.ofNat w (x.toNat - y.toNat)) := by
  intro i hi
  unfold subtract
  rw [AIG.RefVec.denote_ite]
  dsimp only
  have hsx : Represents assign (BVPred.mkUlt aig input).aig
      (input.lhs.cast (AIG.LawfulOperator.le_size (f := BVPred.mkUlt) aig input)) x := by
    intro j hj
    rw [AIG.RefVec.get_cast]
    exact (AIG.LawfulOperator.denote_mem_prefix (f := BVPred.mkUlt) _).trans (hx j hj)
  have hsy : Represents assign (BVPred.mkUlt aig input).aig
      (input.rhs.cast (AIG.LawfulOperator.le_size (f := BVPred.mkUlt) aig input)) y := by
    intro j hj
    rw [AIG.RefVec.get_cast]
    exact (AIG.LawfulOperator.denote_mem_prefix (f := BVPred.mkUlt) _).trans (hy j hj)
  rw [AIG.LawfulVecOperator.denote_cast_entry (f := blastSub),
    BVPred.mkUlt_denote_eq aig x y input assign hx hy, denote_blastConst]
  rw [denote_blastSub (BVPred.mkUlt aig input).aig x y assign
    (input.cast (AIG.LawfulOperator.le_size (f := BVPred.mkUlt) aig input)) hsx hsy]
  by_cases hxy : x.toNat < y.toNat
  · simp [BitVec.ult, hxy, Nat.sub_eq_zero_of_le (Nat.le_of_lt hxy)]
  · have hsub : x - y = BitVec.ofNat w (x.toNat - y.toNat) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub_of_not_usubOverflow (by simpa [BitVec.usubOverflow] using hxy)]
      exact (Nat.mod_eq_of_lt ((Nat.sub_le _ _).trans_lt x.isLt)).symm
    simp [BitVec.ult, hxy, hsub]

theorem subtract_correct (aig : AIG A) (input : AIG.BinaryRefVec aig w)
    (assign : A → Bool) (x y : Nat) (hxf : x < 2 ^ w) (hyf : y < 2 ^ w)
    (hx : Represents assign aig input.lhs (BitVec.ofNat w x))
    (hy : Represents assign aig input.rhs (BitVec.ofNat w y)) :
    RepresentsNat assign (subtract aig input).aig (subtract aig input).vec (x - y) := by
  refine ⟨(Nat.sub_le _ _).trans_lt hxf, ?_⟩
  simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hxf, Nat.mod_eq_of_lt hyf] using
    subtract_bits aig input assign _ _ hx hy

theorem eq_correct (aig : AIG A) (input : AIG.BinaryRefVec aig w)
    (assign : A → Bool) (x y : Nat) (hxf : x < 2 ^ w) (hyf : y < 2 ^ w)
    (hx : Represents assign aig input.lhs (BitVec.ofNat w x))
    (hy : Represents assign aig input.rhs (BitVec.ofNat w y)) :
    AIG.denote assign (BVPred.mkEq aig input) = decide (x = y) := by
  rw [BVPred.mkEq_denote_eq aig input assign _ _ hx hy]
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq, ← BitVec.toNat_inj, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hxf, Nat.mod_eq_of_lt hyf]

theorem lt_correct (aig : AIG A) (input : AIG.BinaryRefVec aig w)
    (assign : A → Bool) (x y : Nat) (hxf : x < 2 ^ w) (hyf : y < 2 ^ w)
    (hx : Represents assign aig input.lhs (BitVec.ofNat w x))
    (hy : Represents assign aig input.rhs (BitVec.ofNat w y)) :
    AIG.denote assign (BVPred.mkUlt aig input) = decide (x < y) := by
  rw [BVPred.mkUlt_denote_eq aig _ _ input assign hx hy]
  simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hxf, Nat.mod_eq_of_lt hyf]

/-- Equality works for any injective fixed-width encoding, including keys and messages. -/
theorem eq_encoded_correct {T : Type} [DecidableEq T] (encode : T → BitVec w)
    (hinj : Function.Injective encode) (aig : AIG A) (input : AIG.BinaryRefVec aig w)
    (assign : A → Bool) (x y : T)
    (hx : Represents assign aig input.lhs (encode x))
    (hy : Represents assign aig input.rhs (encode y)) :
    AIG.denote assign (BVPred.mkEq aig input) = decide (x = y) := by
  rw [BVPred.mkEq_denote_eq aig input assign _ _ hx hy]
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  exact hinj.eq_iff

/-- Reduction into Fin (n+1); a modulus at least the word range needs only wiring. -/
def finOfNat (aig : AIG A) (input : AIG.RefVec aig w) (n : Nat) : AIG.RefVecEntry A w :=
  if 2 ^ w ≤ n + 1 then ⟨aig, input⟩
  else blastUmod aig ⟨input, blastConst aig (BitVec.ofNat w (n + 1))⟩

theorem finOfNat_size (aig : AIG A) (input : AIG.RefVec aig w) (n : Nat) :
    (finOfNat aig input n).aig.decls.size ≤ aig.decls.size + 36 * w * w + 7 * w := by
  unfold finOfNat
  split
  · dsimp only; omega
  · exact BitCircuit.mod_size _ _

theorem finOfNat_correct (aig : AIG A) (input : AIG.RefVec aig w) (n : Nat)
    (assign : A → Bool) (x : Nat) (hxf : x < 2 ^ w)
    (hx : Represents assign aig input (BitVec.ofNat w x)) :
    RepresentsNat assign (finOfNat aig input n).aig (finOfNat aig input n).vec (x % (n + 1)) := by
  refine ⟨(Nat.mod_le _ _).trans_lt hxf, ?_⟩
  by_cases he : 2 ^ w ≤ n + 1
  · have hout : finOfNat aig input n = ⟨aig, input⟩ := by simp [finOfNat, he]
    apply (congrArg (fun r : AIG.RefVecEntry A w =>
      Represents assign r.aig r.vec (BitVec.ofNat w (x % (n + 1)))) hout).mpr
    simpa only [Nat.mod_eq_of_lt (hxf.trans_le he)] using hx
  · have hout : finOfNat aig input n =
        blastUmod aig ⟨input, blastConst aig (BitVec.ofNat w (n + 1))⟩ := by
      simp [finOfNat, he]
    apply (congrArg (fun r : AIG.RefVecEntry A w =>
      Represents assign r.aig r.vec (BitVec.ofNat w (x % (n + 1)))) hout).mpr
    have hn : n + 1 < 2 ^ w := Nat.lt_of_not_ge he
    have heq : BitVec.ofNat w x % BitVec.ofNat w (n + 1) = BitVec.ofNat w (x % (n + 1)) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_umod, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hxf,
        Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt ((Nat.mod_lt _ (Nat.zero_lt_succ n)).trans hn)]
    rw [← heq]
    exact denote_blastUmod aig _ _ assign _ hx (denote_blastConst _ _ _)

/-- Fin values use the same binary word as their natural value, so conversion is wiring. -/
theorem finVal_correct (aig : AIG A) (input : AIG.RefVec aig w) (n : Nat)
    (hn : n + 1 ≤ 2 ^ w) (assign : A → Bool) (x : Fin (n + 1))
    (hx : Represents assign aig input (BitVec.ofNat w x.val)) :
    RepresentsNat assign aig input x.val :=
  ⟨x.isLt.trans_le hn, hx⟩

theorem finZero_correct (aig : AIG A) (assign : A → Bool) (n : Nat) :
    RepresentsNat assign aig (blastConst aig (BitVec.ofNat w 0)) (0 : Fin (n + 1)).val :=
  ⟨Nat.two_pow_pos w, denote_blastConst aig _ assign⟩

end Signatures.Runtime.WordCircuit
