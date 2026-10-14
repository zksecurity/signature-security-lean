import Signatures.Runtime.BitCircuit
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Nat.Size

/-! Concrete prime-field extraction using the standard library's Boolean circuits.
Words are wide enough to hold unreduced products. The cost theorem counts actual
AIG declarations and the correctness theorem relates the output bits to `ZMod`.
Subtraction and Fermat inversion yield a cubic-size extractor for odd prime fields.
This is a scalar-arithmetic component, not a compiler for the full signature machine. -/

namespace Signatures.Runtime.PrimeFieldCircuit

open Std.Sat Std.Tactic.BVDecide BVExpr.bitblast

variable {A : Type} [Hashable A] [DecidableEq A] {w : Nat}

def Represents (assign : A → Bool) (aig : AIG A) (refs : AIG.RefVec aig w)
    (value : BitVec w) : Prop :=
  ∀ i hi, AIG.denote assign ⟨aig, refs.get i hi⟩ = value.getLsbD i

/-- Schoolbook multiplication followed by shift/subtract modular reduction. -/
def mulMod (aig : AIG A) (input : AIG.BinaryRefVec aig w) (p : Nat) : AIG.RefVecEntry A w :=
  let product := blastMul aig input
  blastUmod product.aig ⟨product.vec, blastConst product.aig (BitVec.ofNat w p)⟩

theorem mulMod_size (aig : AIG A) (input : AIG.BinaryRefVec aig w) (p : Nat) :
    (mulMod aig input p).aig.decls.size ≤ aig.decls.size + 51 * w * w + 7 * w := by
  unfold mulMod
  refine (BitCircuit.mod_size _ _).trans ?_
  have := BitCircuit.mul_size aig input
  nlinarith

theorem mulMod_bits (aig : AIG A) (input : AIG.BinaryRefVec aig w) (p : Nat)
    (assign : A → Bool) (x y : BitVec w)
    (hx : Represents assign aig input.lhs x) (hy : Represents assign aig input.rhs y) :
    Represents assign (mulMod aig input p).aig (mulMod aig input p).vec
      ((x * y) % BitVec.ofNat w p) := by
  apply denote_blastUmod
  · exact denote_blastMul aig x y assign input hx hy
  · exact denote_blastConst _ _ _

variable {p : Nat} [Fact p.Prime]

private theorem modulus_lt (hfit : p * p ≤ 2 ^ w) : p < 2 ^ w := by
  have := (Fact.out : p.Prime).two_le
  nlinarith

/-- Encoded field multiplication cannot overflow before reduction at this width. -/
theorem mul_word (hfit : p * p ≤ 2 ^ w) (x y : ZMod p) :
    ((BitVec.ofNat w x.val * BitVec.ofNat w y.val) % BitVec.ofNat w p) =
      BitVec.ofNat w (x * y).val := by
  have hp := modulus_lt hfit
  have hx := x.val_lt
  have hy := y.val_lt
  have hm : x.val * y.val < 2 ^ w := by
    have := Nat.mul_lt_mul_of_lt_of_lt hx hy
    omega
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_umod, BitVec.toNat_mul, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (hx.trans hp), Nat.mod_eq_of_lt (hy.trans hp),
    Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt hm,
    Nat.mod_eq_of_lt ((x * y).val_lt.trans hp)]
  exact (ZMod.val_mul x y).symm

/-- The same circuit whose gate count is bounded computes multiplication in the field. -/
theorem mulMod_correct (hfit : p * p ≤ 2 ^ w) (aig : AIG A)
    (input : AIG.BinaryRefVec aig w) (assign : A → Bool) (x y : ZMod p)
    (hx : Represents assign aig input.lhs (BitVec.ofNat w x.val))
    (hy : Represents assign aig input.rhs (BitVec.ofNat w y.val)) :
    Represents assign (mulMod aig input p).aig (mulMod aig input p).vec
      (BitVec.ofNat w (x * y).val) := by
  rw [← mul_word hfit]
  exact mulMod_bits aig input p assign _ _ hx hy

private theorem prefix_trans {a b c : AIG A}
    (h : AIG.IsPrefix a.decls b.decls) (h' : AIG.IsPrefix b.decls c.decls) :
    AIG.IsPrefix a.decls c.decls where
  size_le := h.size_le.trans h'.size_le
  idx_eq i hi := (h'.idx_eq i (hi.trans_le h.size_le)).trans (h.idx_eq i hi)

/-- A circuit extension, with evidence that existing wires keep their meanings. -/
structure Built (aig : AIG A) (w : Nat) where
  result : AIG.RefVecEntry A w
  extension : AIG.IsPrefix aig.decls result.aig.decls

def Built.cast {aig : AIG A} (out : Built aig w) (refs : AIG.RefVec aig w) :
    AIG.RefVec out.result.aig w := refs.cast out.extension.size_le

def Built.chain {aig : AIG A} (out : Built aig w) (next : Built out.result.aig w) :
    Built aig w := ⟨next.result, prefix_trans out.extension next.extension⟩

theorem Built.preserves {aig : AIG A} (out : Built aig w) (assign : A → Bool)
    (refs : AIG.RefVec aig w) (value : BitVec w) (h : Represents assign aig refs value) :
    Represents assign out.result.aig (out.cast refs) value := by
  intro i hi
  rw [Built.cast, AIG.RefVec.get_cast]
  exact (AIG.denote.eq_of_isPrefix ⟨aig, refs.get i hi⟩ _ out.extension).trans (h i hi)

def multiply (aig : AIG A) (input : AIG.BinaryRefVec aig w) (p : Nat) : Built aig w where
  result := mulMod aig input p
  extension := prefix_trans (AIG.LawfulVecOperator.isPrefix_aig (f := blastMul) aig input)
    (AIG.LawfulVecOperator.isPrefix_aig (f := blastUmod) _ _)

attribute [local irreducible] mulMod

/-- A public little-endian exponent is unrolled; no table indexed by field values is used. -/
def power (aig : AIG A) (input : AIG.RefVec aig w) (p : Nat) : List Bool → Built aig w
  | [] => ⟨⟨aig, blastConst aig (BitVec.ofNat w 1)⟩, AIG.IsPrefix.rfl⟩
  | b :: bs =>
    let tail := power aig input p bs
    let sq := multiply tail.result.aig ⟨tail.result.vec, tail.result.vec⟩ p
    let squared := tail.chain sq
    if b then squared.chain (multiply squared.result.aig ⟨squared.result.vec, squared.cast input⟩ p)
    else squared

def exponent : List Bool → Nat
  | [] => 0
  | b :: bs => exponent bs + exponent bs + b.toNat

theorem exponent_bits (n : Nat) : exponent n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b n hn ih =>
    rw [Nat.bits_append_bit n b hn]
    cases b <;> simp [exponent, ih, Nat.bit] <;> omega

theorem power_size (aig : AIG A) (input : AIG.RefVec aig w) (p : Nat) (bs : List Bool) :
    (power aig input p bs).result.aig.decls.size ≤
      aig.decls.size + 2 * (51 * w * w + 7 * w) * bs.length := by
  induction bs with
  | nil => simp [power]
  | cons b bs ih =>
    have hs := mulMod_size (power aig input p bs).result.aig
      ⟨(power aig input p bs).result.vec, (power aig input p bs).result.vec⟩ p
    cases b
    · simp only [power, Bool.false_eq_true, ↓reduceIte, Built.chain, multiply, List.length_cons]
      nlinarith
    · simp only [power, ↓reduceIte, Built.chain]
      refine (mulMod_size _ _ _).trans ?_
      dsimp only [multiply] at hs ⊢
      simp only [List.length_cons]
      nlinarith

theorem power_correct (hfit : p * p ≤ 2 ^ w) (aig : AIG A) (input : AIG.RefVec aig w)
    (assign : A → Bool) (x : ZMod p) (bs : List Bool)
    (hx : Represents assign aig input (BitVec.ofNat w x.val)) :
    Represents assign (power aig input p bs).result.aig (power aig input p bs).result.vec
      (BitVec.ofNat w (x ^ exponent bs).val) := by
  induction bs with
  | nil =>
    simp only [power, exponent, pow_zero]
    rw [ZMod.val_one]
    exact denote_blastConst _ _ _
  | cons b bs ih =>
    have hs := mulMod_correct hfit (power aig input p bs).result.aig
      ⟨(power aig input p bs).result.vec, (power aig input p bs).result.vec⟩ assign
      (x ^ exponent bs) (x ^ exponent bs) ih ih
    have hx' := ((power aig input p bs).chain
      (multiply (power aig input p bs).result.aig
        ⟨(power aig input p bs).result.vec, (power aig input p bs).result.vec⟩ p)).preserves
          assign input _ hx
    cases b
    · simpa [power, exponent, Built.chain, multiply, pow_add] using hs
    · let sq := (power aig input p bs).chain
        (multiply (power aig input p bs).result.aig
          ⟨(power aig input p bs).result.vec, (power aig input p bs).result.vec⟩ p)
      have hm := mulMod_correct hfit sq.result.aig ⟨sq.result.vec, sq.cast input⟩ assign
        (x ^ exponent bs * x ^ exponent bs) x hs hx'
      simpa [power, exponent, pow_add, Built.chain, multiply, sq] using hm

/-- Fermat inversion, including zero, for odd prime moduli. -/
def inverse (aig : AIG A) (input : AIG.RefVec aig w) (p : Nat) : Built aig w :=
  power aig input p (p - 2).bits

theorem inverse_size (hfit : p * p ≤ 2 ^ w) (aig : AIG A) (input : AIG.RefVec aig w) :
    (inverse aig input p).result.aig.decls.size ≤
      aig.decls.size + 2 * (51 * w * w + 7 * w) * w := by
  have hlen : (p - 2).bits.length ≤ w := by
    rw [Nat.size_eq_bits_len, Nat.size_le]
    exact (Nat.sub_le p 2).trans_lt (modulus_lt hfit)
  exact (power_size aig input p _).trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ hlen) _)

theorem inverse_correct (hfit : p * p ≤ 2 ^ w) (hp : 2 < p) (aig : AIG A)
    (input : AIG.RefVec aig w) (assign : A → Bool) (x : ZMod p)
    (hx : Represents assign aig input (BitVec.ofNat w x.val)) :
    Represents assign (inverse aig input p).result.aig (inverse aig input p).result.vec
      (BitVec.ofNat w x⁻¹.val) := by
  have he : x ^ (p - 2) = x⁻¹ := by
    by_cases hz : x = 0
    · simp [hz, Nat.ne_of_gt (Nat.sub_pos_of_lt hp)]
    · apply mul_left_cancel₀ hz
      rw [mul_inv_cancel₀ hz, ← pow_succ']
      have he : p - 2 + 1 = p - 1 := by omega
      rw [he]
      exact ZMod.pow_card_sub_one_eq_one hz
  simpa only [inverse, exponent_bits, he] using power_correct hfit aig input assign x (p - 2).bits hx

/-- Add the modulus before subtraction, so unsigned subtraction does not underflow. -/
def subtract (aig : AIG A) (input : AIG.BinaryRefVec aig w) (p : Nat) : Built aig w :=
  let added := blastAdd aig ⟨input.lhs, blastConst aig (BitVec.ofNat w p)⟩
  let h₁ := AIG.LawfulVecOperator.isPrefix_aig (f := blastAdd) aig
    ⟨input.lhs, blastConst aig (BitVec.ofNat w p)⟩
  let sub := blastSub added.aig ⟨added.vec, input.rhs.cast h₁.size_le⟩
  let h₂ := AIG.LawfulVecOperator.isPrefix_aig (f := blastSub) added.aig
    ⟨added.vec, input.rhs.cast h₁.size_le⟩
  let reduced := blastUmod sub.aig ⟨sub.vec, blastConst sub.aig (BitVec.ofNat w p)⟩
  let h₃ := AIG.LawfulVecOperator.isPrefix_aig (f := blastUmod) sub.aig
    ⟨sub.vec, blastConst sub.aig (BitVec.ofNat w p)⟩
  ⟨reduced, prefix_trans (prefix_trans h₁ h₂) h₃⟩

theorem subtract_size (aig : AIG A) (input : AIG.BinaryRefVec aig w) (p : Nat) :
    (subtract aig input p).result.aig.decls.size ≤ aig.decls.size + 36 * w * w + 43 * w := by
  unfold subtract
  dsimp only
  refine (BitCircuit.mod_size _ _).trans ?_
  refine (Nat.add_le_add_right (Nat.add_le_add_right (BitCircuit.sub_size _ _) _) _).trans ?_
  have := BitCircuit.add_size aig ⟨input.lhs, blastConst aig (BitVec.ofNat w p)⟩
  omega

theorem subtract_bits (aig : AIG A) (input : AIG.BinaryRefVec aig w) (p : Nat)
    (assign : A → Bool) (x y : BitVec w)
    (hx : Represents assign aig input.lhs x) (hy : Represents assign aig input.rhs y) :
    Represents assign (subtract aig input p).result.aig (subtract aig input p).result.vec
      ((x + BitVec.ofNat w p - y) % BitVec.ofNat w p) := by
  unfold subtract
  apply denote_blastUmod
  · apply denote_blastSub
    · exact denote_blastAdd aig x _ assign _ hx (denote_blastConst _ _ _)
    · intro i hi
      rw [AIG.RefVec.get_cast]
      exact (AIG.LawfulVecOperator.denote_mem_prefix (f := blastAdd) _).trans (hy i hi)
  · exact denote_blastConst _ _ _

theorem sub_word (hfit : p * p ≤ 2 ^ w) (x y : ZMod p) :
    ((BitVec.ofNat w x.val + BitVec.ofNat w p - BitVec.ofNat w y.val) % BitVec.ofNat w p) =
      BitVec.ofNat w (x - y).val := by
  have hp := modulus_lt hfit
  have hp₂ := (Fact.out : p.Prime).two_le
  have hx := x.val_lt
  have hy := y.val_lt
  have hsum : x.val + p < 2 ^ w := by nlinarith
  have hcast : ((x.val + p - y.val : Nat) : ZMod p) = x - y := by
    rw [Nat.cast_sub (by omega)]
    simp
  have hval : (x.val + p - y.val) % p = (x - y).val := by
    simpa using congrArg ZMod.val hcast
  have hadd : (BitVec.ofNat w x.val + BitVec.ofNat w p).toNat = x.val + p := by
    simp [BitVec.toNat_add, Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt (hx.trans hp),
      Nat.mod_eq_of_lt hsum]
  have hsub : ¬ (BitVec.ofNat w x.val + BitVec.ofNat w p).usubOverflow (BitVec.ofNat w y.val) := by
    simp only [BitVec.usubOverflow, hadd, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (hy.trans hp), decide_eq_true_eq]
    omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_umod, BitVec.toNat_sub_of_not_usubOverflow hsub, hadd]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hy.trans hp), Nat.mod_eq_of_lt hp,
    Nat.mod_eq_of_lt ((x - y).val_lt.trans hp), hval]

theorem subtract_correct (hfit : p * p ≤ 2 ^ w) (aig : AIG A)
    (input : AIG.BinaryRefVec aig w) (assign : A → Bool) (x y : ZMod p)
    (hx : Represents assign aig input.lhs (BitVec.ofNat w x.val))
    (hy : Represents assign aig input.rhs (BitVec.ofNat w y.val)) :
    Represents assign (subtract aig input p).result.aig (subtract aig input p).result.vec
      (BitVec.ofNat w (x - y).val) := by
  rw [← sub_word hfit]
  exact subtract_bits aig input p assign _ _ hx hy

attribute [local irreducible] subtract inverse

/-- Division uses the concrete inversion circuit, followed by modular multiplication. -/
def divide (aig : AIG A) (num den : AIG.RefVec aig w) (p : Nat) : AIG.RefVecEntry A w :=
  let inv := inverse aig den p
  mulMod inv.result.aig ⟨inv.cast num, inv.result.vec⟩ p

theorem divide_size (hfit : p * p ≤ 2 ^ w) (aig : AIG A) (num den : AIG.RefVec aig w) :
    (divide aig num den p).aig.decls.size ≤
      aig.decls.size + 2 * (51 * w * w + 7 * w) * w + (51 * w * w + 7 * w) := by
  unfold divide
  refine (mulMod_size _ _ _).trans ?_
  have := inverse_size hfit aig den
  omega

theorem divide_correct (hfit : p * p ≤ 2 ^ w) (hp : 2 < p) (aig : AIG A)
    (num den : AIG.RefVec aig w) (assign : A → Bool) (x y : ZMod p)
    (hx : Represents assign aig num (BitVec.ofNat w x.val))
    (hy : Represents assign aig den (BitVec.ofNat w y.val)) :
    Represents assign (divide aig num den p).aig (divide aig num den p).vec
      (BitVec.ofNat w (x / y).val) := by
  let inv := inverse aig den p
  have hi := inverse_correct hfit hp aig den assign y hy
  have hm := mulMod_correct hfit inv.result.aig ⟨inv.cast num, inv.result.vec⟩ assign x y⁻¹
    (inv.preserves assign num _ hx) hi
  rw [div_eq_mul_inv]
  exact hm

attribute [local irreducible] divide

private def finishExtract (aig : AIG A) (num c c' : AIG.RefVec aig w) (p : Nat) :
    AIG.RefVecEntry A w :=
  let den := subtract aig ⟨c, c'⟩ p
  divide den.result.aig (den.cast num) den.result.vec p

private theorem finishExtract_size (hfit : p * p ≤ 2 ^ w) (aig : AIG A)
    (num c c' : AIG.RefVec aig w) :
    (finishExtract aig num c c' p).aig.decls.size ≤
      aig.decls.size + (36 * w * w + 43 * w) +
        2 * (51 * w * w + 7 * w) * w + (51 * w * w + 7 * w) := by
  unfold finishExtract
  refine (divide_size hfit _ _ _).trans ?_
  have := subtract_size aig ⟨c, c'⟩ p
  omega

private theorem finishExtract_correct (hfit : p * p ≤ 2 ^ w) (hp : 2 < p) (aig : AIG A)
    (num cr cr' : AIG.RefVec aig w) (assign : A → Bool) (x c c' : ZMod p)
    (hx : Represents assign aig num (BitVec.ofNat w x.val))
    (hc : Represents assign aig cr (BitVec.ofNat w c.val))
    (hc' : Represents assign aig cr' (BitVec.ofNat w c'.val)) :
    Represents assign (finishExtract aig num cr cr' p).aig (finishExtract aig num cr cr' p).vec
      (BitVec.ofNat w (x / (c - c')).val) := by
  let den := subtract aig ⟨cr, cr'⟩ p
  exact divide_correct hfit hp den.result.aig (den.cast num) den.result.vec assign x (c - c')
    (den.preserves assign num _ hx) (subtract_correct hfit aig ⟨cr, cr'⟩ assign c c' hc hc')

attribute [local irreducible] finishExtract

/-- Deterministic two-transcript extraction. Acceptance and distinct-challenge checks
belong to the caller, as in the arithmetic-machine extractor. -/
def extract (aig : AIG A) (z z' c c' : AIG.RefVec aig w) (p : Nat) : AIG.RefVecEntry A w :=
  let num := subtract aig ⟨z, z'⟩ p
  finishExtract num.result.aig num.result.vec (num.cast c) (num.cast c') p

/-- A cubic bound in the encoding width, on the actual generated Boolean circuit. -/
theorem extract_size (hfit : p * p ≤ 2 ^ w) (aig : AIG A)
    (z z' c c' : AIG.RefVec aig w) :
    (extract aig z z' c c' p).aig.decls.size ≤
      aig.decls.size + 102 * w ^ 3 + 137 * w ^ 2 + 93 * w := by
  unfold extract
  refine (finishExtract_size hfit _ _ _ _).trans ?_
  have := subtract_size aig ⟨z, z'⟩ p
  nlinarith

/-- Correctness and cost refer to the same circuit; no field operation remains a gate. -/
theorem extract_correct (hfit : p * p ≤ 2 ^ w) (hp : 2 < p) (aig : AIG A)
    (zr zr' cr cr' : AIG.RefVec aig w) (assign : A → Bool) (z z' c c' : ZMod p)
    (hz : Represents assign aig zr (BitVec.ofNat w z.val))
    (hz' : Represents assign aig zr' (BitVec.ofNat w z'.val))
    (hc : Represents assign aig cr (BitVec.ofNat w c.val))
    (hc' : Represents assign aig cr' (BitVec.ofNat w c'.val)) :
    Represents assign (extract aig zr zr' cr cr' p).aig
      (extract aig zr zr' cr cr' p).vec
      (BitVec.ofNat w ((z - z') / (c - c')).val) := by
  let num := subtract aig ⟨zr, zr'⟩ p
  exact finishExtract_correct hfit hp num.result.aig num.result.vec (num.cast cr) (num.cast cr')
    assign (z - z') c c' (subtract_correct hfit aig ⟨zr, zr'⟩ assign z z' hz hz')
    (num.preserves assign cr _ hc) (num.preserves assign cr' _ hc')

/-- Twice the modulus bit length always accommodates unreduced products. -/
theorem standard_width (p : Nat) : p * p ≤ 2 ^ (2 * p.size) := by
  rw [two_mul, pow_add]
  exact Nat.mul_le_mul (Nat.le_of_lt (Nat.lt_size_self p)) (Nat.le_of_lt (Nat.lt_size_self p))

end Signatures.Runtime.PrimeFieldCircuit
