import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit
import Mathlib.Tactic.Linarith

/-! Size bounds for the standard library's verified Boolean arithmetic circuits.
The measure is the number of AIG declarations, not Lean execution time. Inverted
edges and wiring allocate no gates. These bounds do not yet compile the signature
machine or justify its sampling and group-operation prices. -/

namespace Signatures.Runtime.BitCircuit

open Std.Sat Std.Tactic.BVDecide BVExpr.bitblast

variable {A : Type} [Hashable A] [DecidableEq A]

theorem gate_size (aig : AIG A) (input : AIG.BinaryInput aig) :
    (aig.mkGateCached input).aig.decls.size ≤ aig.decls.size + 1 := by
  have go (aig : AIG A) (input : AIG.BinaryInput aig) :
      (AIG.mkGateCached.go aig input).aig.decls.size ≤ aig.decls.size + 1 := by
    cases aig
    unfold AIG.mkGateCached.go
    dsimp only
    repeat' first | omega | split | (simp only [Array.size_push])
  unfold AIG.mkGateCached
  dsimp only
  split <;> apply go

theorem and_size (aig : AIG A) (input : AIG.BinaryInput aig) :
    (aig.mkAndCached input).aig.decls.size ≤ aig.decls.size + 1 :=
  gate_size aig input

theorem or_size (aig : AIG A) (input : AIG.BinaryInput aig) :
    (aig.mkOrCached input).aig.decls.size ≤ aig.decls.size + 1 :=
  gate_size aig _

theorem xor_size (aig : AIG A) (input : AIG.BinaryInput aig) :
    (aig.mkXorCached input).aig.decls.size ≤ aig.decls.size + 3 := by
  unfold AIG.mkXorCached
  dsimp only
  refine (gate_size _ _).trans ?_
  have h₂ := gate_size (aig.mkGateCached input).aig
    ((input.cast (AIG.LawfulOperator.le_size (f := AIG.mkGateCached) aig input)).invert true true)
  have h₁ := gate_size aig input
  omega

theorem fullAdderOut_size (aig : AIG A) (input : FullAdderInput aig) :
    (mkFullAdderOut aig input).aig.decls.size ≤ aig.decls.size + 6 := by
  unfold mkFullAdderOut
  dsimp only
  refine (xor_size _ _).trans ?_
  have := xor_size aig ⟨input.lhs, input.rhs⟩
  omega

theorem fullAdderCarry_size (aig : AIG A) (input : FullAdderInput aig) :
    (mkFullAdderCarry aig input).aig.decls.size ≤ aig.decls.size + 6 := by
  unfold mkFullAdderCarry
  dsimp only
  refine (or_size _ _).trans ?_
  refine (Nat.add_le_add_right (and_size _ _) 1).trans ?_
  refine (Nat.add_le_add_right (Nat.add_le_add_right (and_size _ _) 1) 1).trans ?_
  have := xor_size aig ⟨input.lhs, input.rhs⟩
  omega

theorem fullAdder_size (aig : AIG A) (input : FullAdderInput aig) :
    (mkFullAdder aig input).aig.decls.size ≤ aig.decls.size + 12 := by
  unfold mkFullAdder
  dsimp only
  refine (fullAdderCarry_size _ _).trans ?_
  have := fullAdderOut_size aig input
  omega

theorem add_go_size {w : Nat} (aig : AIG A) (lhs rhs : AIG.RefVec aig w)
    (curr : Nat) (hcurr : curr ≤ w) (cin : AIG.Ref aig) (s : AIG.RefVec aig curr) :
    (blastAdd.go aig lhs rhs curr hcurr cin s).aig.decls.size ≤
      aig.decls.size + 12 * (w - curr) := by
  rw [blastAdd.go]
  split
  · dsimp only
    refine (add_go_size _ _ _ _ _ _ _).trans ?_
    have := fullAdder_size aig ⟨lhs.get curr ‹curr < w›, rhs.get curr ‹curr < w›, cin⟩
    omega
  · simp
termination_by w - curr

/-- The library's verified ripple-carry adder allocates at most 12 gates per bit. -/
theorem add_size {w : Nat} (aig : AIG A) (input : AIG.BinaryRefVec aig w) :
    (blastAdd aig input).aig.decls.size ≤ aig.decls.size + 12 * w := by
  unfold blastAdd
  split <;> simpa only [blastAdd.blast, Nat.sub_zero] using add_go_size aig _ _ 0 _ _ _

theorem if_size (aig : AIG A) (input : AIG.TernaryInput aig) :
    (aig.mkIfCached input).aig.decls.size ≤ aig.decls.size + 3 := by
  unfold AIG.mkIfCached
  dsimp only [AIG.mkNotCached]
  refine (or_size _ _).trans ?_
  refine (Nat.add_le_add_right (and_size _ _) 1).trans ?_
  have := and_size aig ⟨input.discr, input.lhs⟩
  omega

private theorem ite_go_size {w : Nat} (aig : AIG A) (curr : Nat) (hcurr : curr ≤ w)
    (discr : AIG.Ref aig) (lhs rhs : AIG.RefVec aig w) (s : AIG.RefVec aig curr) :
    (AIG.RefVec.ite.go aig curr hcurr discr lhs rhs s).aig.decls.size ≤
      aig.decls.size + 3 * (w - curr) := by
  rw [AIG.RefVec.ite.go]
  split
  · dsimp only
    refine (ite_go_size _ _ _ _ _ _ _).trans ?_
    have := if_size aig ⟨discr, lhs.get curr ‹curr < w›, rhs.get curr ‹curr < w›⟩
    omega
  · simp
termination_by w - curr

theorem ite_size {w : Nat} (aig : AIG A) (input : AIG.RefVec.IfInput aig w) :
    (AIG.RefVec.ite aig input).aig.decls.size ≤ aig.decls.size + 3 * w := by
  simpa only [AIG.RefVec.ite, Nat.sub_zero] using ite_go_size aig 0 _ _ _ _ _

private theorem not_go_size {w : Nat} (aig : AIG A) (idx : Nat) (hidx : idx ≤ w)
    (s : AIG.RefVec aig idx) (input : AIG.RefVec aig w) :
    (AIG.RefVec.map.go aig idx hidx s input AIG.mkNotCached).aig.decls.size = aig.decls.size := by
  rw [AIG.RefVec.map.go]
  split
  · exact not_go_size _ _ _ _ _
  · rfl
termination_by w - idx

theorem not_size {w : Nat} (aig : AIG A) (input : AIG.RefVec aig w) :
    (blastNot aig input).aig.decls.size = aig.decls.size :=
  not_go_size aig 0 _ _ input

theorem neg_size {w : Nat} (aig : AIG A) (input : AIG.RefVec aig w) :
    (blastNeg aig input).aig.decls.size ≤ aig.decls.size + 12 * w := by
  unfold blastNeg
  dsimp only
  refine (add_size _ _).trans ?_
  rw [not_size]

theorem sub_size {w : Nat} (aig : AIG A) (input : AIG.BinaryRefVec aig w) :
    (blastSub aig input).aig.decls.size ≤ aig.decls.size + 24 * w := by
  unfold blastSub
  dsimp only
  refine (add_size _ _).trans ?_
  have := neg_size aig input.rhs
  omega

private theorem shift_go_size {w : Nat} (aig : AIG A) (input : AIG.RefVec aig w)
    (distance curr : Nat) (hcurr : curr ≤ w) (s : AIG.RefVec aig curr) :
    (blastShiftLeftConst.go aig input distance curr hcurr s).aig.decls.size = aig.decls.size := by
  rw [blastShiftLeftConst.go]
  split
  · split <;> exact shift_go_size _ _ _ _ _ _
  · rfl
termination_by w - curr

theorem shift_size {w : Nat} (aig : AIG A) (input : AIG.ShiftTarget aig w) :
    (blastShiftLeftConst aig input).aig.decls.size = aig.decls.size :=
  shift_go_size aig input.vec input.distance 0 _ _

private theorem mul_go_size {w : Nat} (aig : AIG A) (lhs rhs : AIG.RefVec aig w)
    (curr : Nat) (acc : AIG.RefVec aig w) :
    (blastMul.go aig lhs rhs curr acc).aig.decls.size ≤
      aig.decls.size + 15 * w * (w - curr) := by
  rw [blastMul.go]
  split
  · split
    · refine (mul_go_size _ _ _ _ _).trans ?_
      exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _
    · dsimp only
      refine (mul_go_size _ _ _ _ _).trans ?_
      refine (Nat.add_le_add_right (ite_size _ _) _).trans ?_
      refine (Nat.add_le_add_right (Nat.add_le_add_right (add_size _ _) _) _).trans ?_
      rw [shift_size]
      have : w - curr = w - (curr + 1) + 1 := by omega
      rw [this, Nat.mul_add]
      omega
  · simp
termination_by w - curr

/-- Schoolbook multiplication has a quadratic bound in the word width, not its value. -/
theorem mul_size {w : Nat} (aig : AIG A) (input : AIG.BinaryRefVec aig w) :
    (blastMul aig input).aig.decls.size ≤ aig.decls.size + 15 * w * w := by
  have blast (input : AIG.BinaryRefVec aig w) :
      (blastMul.blast aig input).aig.decls.size ≤ aig.decls.size + 15 * w * w := by
    unfold blastMul.blast
    split
    · simp
    · dsimp only
      refine (mul_go_size _ _ _ _ _).trans ?_
      have h := ite_size aig ⟨input.rhs.get 0 (by omega), input.lhs, blastConst aig 0⟩
      have : w = (w - 1) + 1 := by omega
      nlinarith
  unfold blastMul
  split <;> apply blast

private theorem overflow_go_size {w : Nat} (aig : AIG A) (lhs rhs : AIG.RefVec aig w)
    (curr : Nat) (cin : AIG.Ref aig) :
    (mkOverflowBit.go aig lhs rhs curr cin).aig.decls.size ≤ aig.decls.size + 6 * (w - curr) := by
  rw [mkOverflowBit.go]
  split
  · dsimp only
    refine (overflow_go_size _ _ _ _ _).trans ?_
    have := fullAdderCarry_size aig ⟨lhs.get curr ‹curr < w›, rhs.get curr ‹curr < w›, cin⟩
    omega
  · simp
termination_by w - curr

theorem overflow_size (aig : AIG A) (input : OverflowInput aig) :
    (mkOverflowBit aig input).aig.decls.size ≤ aig.decls.size + 6 * input.w := by
  simpa only [mkOverflowBit, Nat.sub_zero] using overflow_go_size aig _ _ 0 _

theorem ult_size {w : Nat} (aig : AIG A) (input : AIG.BinaryRefVec aig w) :
    (BVPred.mkUlt aig input).aig.decls.size ≤ aig.decls.size + 6 * w := by
  unfold BVPred.mkUlt
  dsimp only [AIG.mkNotCached]
  refine (overflow_size _ _).trans ?_
  rw [not_size]

theorem beq_size (aig : AIG A) (input : AIG.BinaryInput aig) :
    (aig.mkBEqCached input).aig.decls.size ≤ aig.decls.size + 3 := by
  unfold AIG.mkBEqCached
  dsimp only
  refine (gate_size _ _).trans ?_
  refine (Nat.add_le_add_right (gate_size _ _) 1).trans ?_
  have := gate_size aig (input.invert false true)
  omega

private theorem zip_go_size {w : Nat} (aig : AIG A) (idx : Nat) (s : AIG.RefVec aig idx)
    (hidx : idx ≤ w) (lhs rhs : AIG.RefVec aig w)
    (f : (aig : AIG A) → AIG.BinaryInput aig → AIG.Entrypoint A)
    [AIG.LawfulOperator A AIG.BinaryInput f] [AIG.RefVec.LawfulZipOperator A f]
    (price : Nat) (bound : ∀ aig input, (f aig input).aig.decls.size ≤ aig.decls.size + price) :
    (AIG.RefVec.zip.go aig idx s hidx lhs rhs f).aig.decls.size ≤
      aig.decls.size + price * (w - idx) := by
  rw [AIG.RefVec.zip.go]
  split
  · dsimp only
    refine (zip_go_size _ _ _ _ _ _ f price bound).trans ?_
    have := bound aig ⟨lhs.get idx ‹idx < w›, rhs.get idx ‹idx < w›⟩
    have : w - idx = (w - (idx + 1)) + 1 := by omega
    rw [this, Nat.mul_add]
    omega
  · simp
termination_by w - idx

theorem zip_size {w : Nat} (aig : AIG A) (input : AIG.BinaryRefVec aig w)
    (f : (aig : AIG A) → AIG.BinaryInput aig → AIG.Entrypoint A)
    [AIG.LawfulOperator A AIG.BinaryInput f] [AIG.RefVec.LawfulZipOperator A f]
    (price : Nat) (bound : ∀ aig input, (f aig input).aig.decls.size ≤ aig.decls.size + price) :
    (AIG.RefVec.zip aig input f).aig.decls.size ≤ aig.decls.size + price * w := by
  simpa only [AIG.RefVec.zip, Nat.sub_zero] using zip_go_size aig 0 _ _ _ _ f price bound

private theorem fold_go_size {w : Nat} (aig : AIG A) (acc : AIG.Ref aig) (idx : Nat)
    (input : AIG.RefVec aig w)
    (f : (aig : AIG A) → AIG.BinaryInput aig → AIG.Entrypoint A)
    [AIG.LawfulOperator A AIG.BinaryInput f]
    (price : Nat) (bound : ∀ aig input, (f aig input).aig.decls.size ≤ aig.decls.size + price) :
    (AIG.RefVec.fold.go aig acc idx w input f).aig.decls.size ≤
      aig.decls.size + price * (w - idx) := by
  rw [AIG.RefVec.fold.go]
  split
  · dsimp only
    refine (fold_go_size _ _ _ _ f price bound).trans ?_
    have := bound aig ⟨acc, input.get idx ‹idx < w›⟩
    have : w - idx = (w - (idx + 1)) + 1 := by omega
    rw [this, Nat.mul_add]
    omega
  · simp
termination_by w - idx

theorem fold_size {w : Nat} (aig : AIG A) (input : AIG.RefVec aig w)
    (f : (aig : AIG A) → AIG.BinaryInput aig → AIG.Entrypoint A)
    [AIG.LawfulOperator A AIG.BinaryInput f]
    (price : Nat) (bound : ∀ aig input, (f aig input).aig.decls.size ≤ aig.decls.size + price) :
    (AIG.RefVec.fold aig input f).aig.decls.size ≤ aig.decls.size + price * w := by
  simpa only [AIG.RefVec.fold, Nat.sub_zero] using fold_go_size aig _ 0 input f price bound

theorem eq_size {w : Nat} (aig : AIG A) (input : AIG.BinaryRefVec aig w) :
    (BVPred.mkEq aig input).aig.decls.size ≤ aig.decls.size + 4 * w := by
  unfold BVPred.mkEq
  dsimp only
  refine (fold_size _ _ _ 1 and_size).trans ?_
  have := zip_size aig input _ 3 beq_size
  omega

private theorem extend_go_size (aig : AIG A) (w : Nat) (input : AIG.RefVec aig w)
    (newWidth curr : Nat) (hcurr : curr ≤ newWidth) (s : AIG.RefVec aig curr) :
    (blastZeroExtend.go aig w input newWidth curr hcurr s).aig.decls.size = aig.decls.size := by
  rw [blastZeroExtend.go]
  split
  · split <;> exact extend_go_size _ _ _ _ _ _ _
  · rfl
termination_by newWidth - curr

theorem extend_size {w : Nat} (aig : AIG A) (input : AIG.ExtendTarget aig w) :
    (blastZeroExtend aig input).aig.decls.size = aig.decls.size :=
  extend_go_size aig _ _ w 0 _ _

theorem shiftConcat_size {w : Nat} (aig : AIG A) (input : blastUdiv.ShiftConcatInput aig w) :
    (blastUdiv.blastShiftConcat aig input).aig.decls.size = aig.decls.size :=
  extend_size aig _

private theorem divStep_size {w : Nat} (aig : AIG A) (n d : AIG.RefVec aig w)
    (wn wr : Nat) (q r : AIG.RefVec aig w) :
    (blastUdiv.blastDivSubtractShift aig n d wn wr q r).aig.decls.size ≤
      aig.decls.size + 36 * w := by
  unfold blastUdiv.blastDivSubtractShift
  dsimp only
  refine (ite_size _ _).trans ?_
  refine (Nat.add_le_add_right (ite_size _ _) _).trans ?_
  refine (Nat.add_le_add_right (Nat.add_le_add_right (ult_size _ _) _) _).trans ?_
  refine (Nat.add_le_add_right (Nat.add_le_add_right
    (Nat.add_le_add_right (sub_size _ _) _) _) _).trans ?_
  rw [shiftConcat_size, shiftConcat_size, shiftConcat_size]
  omega

private theorem div_go_size {w : Nat} (aig : AIG A) (curr : Nat) (n d : AIG.RefVec aig w)
    (wn wr : Nat) (q r : AIG.RefVec aig w) :
    (blastUdiv.go aig curr n d wn wr q r).aig.decls.size ≤ aig.decls.size + 36 * w * curr := by
  cases curr with
  | zero => simp [blastUdiv.go]
  | succ curr =>
    simp only [blastUdiv.go]
    refine (div_go_size _ _ _ _ _ _ _ _).trans ?_
    have := divStep_size aig n d wn wr q r
    rw [Nat.mul_succ]
    omega

/-- The standard shift/subtract remainder circuit has a quadratic gate bound. -/
theorem mod_size {w : Nat} (aig : AIG A) (input : AIG.BinaryRefVec aig w) :
    (blastUmod aig input).aig.decls.size ≤ aig.decls.size + 36 * w * w + 7 * w := by
  unfold blastUmod
  dsimp only
  refine (ite_size _ _).trans ?_
  refine (Nat.add_le_add_right (div_go_size _ _ _ _ _ _ _ _) _).trans ?_
  have := eq_size aig ⟨input.rhs, blastConst aig 0#w⟩
  omega

end Signatures.Runtime.BitCircuit
