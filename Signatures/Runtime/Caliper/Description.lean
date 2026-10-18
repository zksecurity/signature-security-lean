import Signatures.Runtime.Caliper.Program

/-! Stored code is charged after expanding library calls. The prefix description
includes instruction tags, operation tags, register/buffer names and immediates.
Every token must fit a machine word; arbitrary natural-number operands therefore
cannot hide unbounded static information in a single word.
-/

namespace Signatures.Runtime.CaliperBackend

open Caliper

private def unaryTag : UnOp → Nat
  | .not => 0 | .neg => 1 | .isZero => 2 | .isNonZero => 3

private def binaryTag : BinOp → Nat
  | .add => 0 | .sub => 1 | .mul => 2 | .mulhi => 3
  | .udiv => 4 | .umod => 5 | .and => 6 | .or => 7 | .xor => 8
  | .shl => 9 | .shr => 10 | .eq => 11 | .ne => 12 | .ult => 13 | .ule => 14

variable {w : Nat}

/-- A prefix description: each tag fixes the number of operands and subtrees.
Calls are inlined before serialization, so each occurrence pays for its code. -/
def description : Stmt w → List Nat
  | .skip => [0]
  | .seq first second => 1 :: (description first ++ description second)
  | .imm dst value => [2, dst, value.toNat]
  | .rand dst => [3, dst]
  | .mov dst src => [4, dst, src]
  | .un op dst src => [5, unaryTag op, dst, src]
  | .bin op dst left right => [6, binaryTag op, dst, left, right]
  | .memAlloc buf size => [7, buf, size]
  | .memAllocI buf size => [8, buf, size]
  | .memFree buf => [9, buf]
  | .memLen dst buf => [10, dst, buf]
  | .memLoad dst buf index => [11, dst, buf, index]
  | .memStore buf index src => [12, buf, index, src]
  | .memPush buf src => [13, buf, src]
  | .memPop buf => [14, buf]
  | .ifNZ condition yes no => 15 :: condition :: (description yes ++ description no)
  | .whileNZ guard condition body => 16 :: condition :: (description guard ++ description body)

/-- A sufficient, explicit address-width condition on stored program operands. -/
def DescriptionFits (code : Stmt w) : Prop :=
  ∀ token ∈ description code, token < 2 ^ w

def descriptionWords (code : Stmt w) : Nat := (description code).length

theorem descriptionWords_seq (first second : Stmt w) :
    descriptionWords (.seq first second) = descriptionWords first + descriptionWords second + 1 := by
  simp [descriptionWords, description]

theorem DescriptionFits.seq {first second : Stmt w} (hw : 0 < w)
    (hf : DescriptionFits first) (hs : DescriptionFits second) :
    DescriptionFits (.seq first second) := by
  intro token ht
  simp only [description, List.mem_cons, List.mem_append] at ht
  rcases ht with rfl | ht | ht
  · exact Nat.one_lt_two_pow hw.ne'
  · exact hf token ht
  · exact hs token ht

def Program.descriptionWords {Call : Type} (library : Library w Call)
    (program : Program w Call) : Nat :=
  CaliperBackend.descriptionWords (program.lower library)

end Signatures.Runtime.CaliperBackend
