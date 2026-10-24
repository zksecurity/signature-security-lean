import Proofs.Runtime.FieldProgram
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Tactic.FinCases

/-! Complete affine elliptic-curve operations as straight-line field code.
The encoding is (finite flag, x, y), with (0,0,0) for infinity. Its semantics
are the existing mathlib point group, including infinity and vertical lines.
The field-code compiler supplies concrete circuits, not a group-operation oracle. -/

namespace Signatures.Runtime.EllipticCurveCode

open FieldProgram WeierstrassCurve

variable {p : Nat} [Fact p.Prime]

def encode {W : Affine (ZMod p)} : W.Point → Fin 3 → ZMod p
  | .zero => ![0, 0, 0]
  | .some x y _ => ![1, x, y]

theorem encode_injective (W : Affine (ZMod p)) : Function.Injective (@encode p _ W) := by
  intro P Q h
  cases P with
  | zero =>
    cases Q with
    | zero => rfl
    | some x y hq => have := congrFun h 0; simp [encode] at this
  | some x y hp =>
    cases Q with
    | zero => have := congrFun h 0; simp [encode] at this
    | some x' y' hq =>
      have hx := congrFun h 1
      have hy := congrFun h 2
      simp only [encode, Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val_two] at hx hy
      cases hx
      cases hy
      rfl

def constant {n : Nat} (x : ZMod p) : Code n := .lit x.val

theorem eval_constant {n : Nat} (x : ZMod p) (env : Fin n → ZMod p) :
    (constant x).eval env = x := by simp [constant, Code.eval]

def negY {n : Nat} (W : Affine (ZMod p)) (x y : Code n) : Code n :=
  -y - constant W.a₁ * x - constant W.a₃

def slope {n : Nat} (W : Affine (ZMod p)) (x₁ x₂ y₁ y₂ : Code n) : Code n :=
  Code.ifEq x₁ x₂ (Code.ifEq y₁ (negY W x₂ y₂) 0
    ((3 * x₁ * x₁ + 2 * constant W.a₂ * x₁ + constant W.a₄ - constant W.a₁ * y₁) /
      (y₁ - negY W x₁ y₁))) ((y₁ - y₂) / (x₁ - x₂))

def addX {n : Nat} (W : Affine (ZMod p)) (x₁ x₂ l : Code n) : Code n :=
  l * l + constant W.a₁ * l - constant W.a₂ - x₁ - x₂

def addY {n : Nat} (W : Affine (ZMod p)) (x₁ x₂ y₁ l : Code n) : Code n :=
  negY W (addX W x₁ x₂ l) (l * (addX W x₁ x₂ l - x₁) + y₁)

theorem eval_negY {n : Nat} (W : Affine (ZMod p)) (x y : Code n) (env : Fin n → ZMod p) :
    (negY W x y).eval env = W.negY (x.eval env) (y.eval env) := by
  simp [negY, eval_constant, Affine.negY]

theorem eval_slope {n : Nat} (W : Affine (ZMod p)) (x₁ x₂ y₁ y₂ : Code n)
    (env : Fin n → ZMod p) :
    (slope W x₁ x₂ y₁ y₂).eval env = W.slope (x₁.eval env) (x₂.eval env) (y₁.eval env) (y₂.eval env) := by
  simp [slope, Code.eval_ifEq, eval_negY, Code.eval, BinOp.eval, eval_constant,
    Affine.slope, pow_two, mul_assoc]

theorem eval_addX {n : Nat} (W : Affine (ZMod p)) (x₁ x₂ l : Code n) (env : Fin n → ZMod p) :
    (addX W x₁ x₂ l).eval env = W.addX (x₁.eval env) (x₂.eval env) (l.eval env) := by
  simp [addX, eval_constant, Affine.addX, pow_two]

theorem eval_addY {n : Nat} (W : Affine (ZMod p)) (x₁ x₂ y₁ l : Code n)
    (env : Fin n → ZMod p) :
    (addY W x₁ x₂ y₁ l).eval env = W.addY (x₁.eval env) (x₂.eval env) (y₁.eval env) (l.eval env) := by
  simp [addY, eval_negY, eval_addX, Affine.addY, Affine.negAddY]

def negCode (W : Affine (ZMod p)) : Fin 3 → Code 3 :=
  ![.var 0, .var 1, Code.ifEq (.var 0) 0 0 (negY W (.var 1) (.var 2))]

theorem negCode_correct (W : Affine (ZMod p)) (P : W.Point) (i : Fin 3) :
    (negCode W i).eval (encode P) = encode (-P) i := by
  cases P <;> fin_cases i <;>
    simp [negCode, Code.eval_ifEq, eval_negY, Code.eval, encode, Affine.Point.neg_def, Affine.Point.neg]

def inputs {W : Affine (ZMod p)} (P Q : W.Point) : Fin 6 → ZMod p :=
  ![encode P 0, encode P 1, encode P 2, encode Q 0, encode Q 1, encode Q 2]

def finiteAdd (W : Affine (ZMod p)) : Fin 3 → Code 6 :=
  let l := slope W (.var 1) (.var 4) (.var 2) (.var 5)
  ![1, addX W (.var 1) (.var 4) l, addY W (.var 1) (.var 4) (.var 2) l]

def addCode (W : Affine (ZMod p)) (i : Fin 3) : Code 6 :=
  Code.ifEq (.var 0) 0 (.var (Fin.natAdd 3 i))
    (Code.ifEq (.var 3) 0 (.var (Fin.castAdd 3 i))
      (Code.ifEq (.var 1) (.var 4)
        (Code.ifEq (.var 2) (negY W (.var 4) (.var 5)) 0 (finiteAdd W i))
        (finiteAdd W i)))

theorem addCode_correct (W : Affine (ZMod p)) (P Q : W.Point) (i : Fin 3) :
    (addCode W i).eval (inputs P Q) = encode (P + Q) i := by
  cases P with
  | zero =>
    fin_cases i <;> simp [addCode, Code.eval_ifEq, Code.eval, inputs, encode,
      Affine.Point.add_def, Affine.Point.add]
  | some x₁ y₁ h₁ =>
    cases Q with
    | zero => fin_cases i <;> simp [addCode, Code.eval_ifEq, Code.eval, inputs, encode,
        Affine.Point.add_def, Affine.Point.add]
    | some x₂ y₂ h₂ =>
      by_cases hx : x₁ = x₂
      · by_cases hy : y₁ = W.negY x₂ y₂
        · fin_cases i <;> simp [addCode, Code.eval_ifEq, Code.eval, eval_negY, inputs,
            encode, Affine.Point.add_def, Affine.Point.add, hx, hy]
        · simp only [Affine.negY] at hy
          fin_cases i <;> simp [addCode, Code.eval_ifEq, finiteAdd, eval_addX, eval_addY,
            eval_slope, eval_negY, Code.eval, inputs, encode,
            Affine.Point.add_def, Affine.Point.add, hx, hy]
      · fin_cases i <;> simp [addCode, Code.eval_ifEq, finiteAdd, eval_addX, eval_addY,
          eval_slope, Code.eval, inputs, encode,
          Affine.Point.add_def, Affine.Point.add, hx]

omit [Fact p.Prime] in
theorem negCode_gates (W : Affine (ZMod p)) (w : Nat) :
    ∑ i, (negCode W i).gates w = 159 * w * w + 143 * w := by
  simp [Fin.sum_univ_succ, negCode, negY, constant, Code.gates_ifEq, Code.gates, BinOp.gates]
  ring

omit [Fact p.Prime] in
theorem addCode_gates (W : Affine (ZMod p)) (w : Nat) :
    ∑ i, (addCode W i).gates w = 4080 * w^3 + 20897 * w^2 + 12774 * w := by
  simp [Fin.sum_univ_succ, addCode, finiteAdd, addY, addX, slope, negY, constant,
    Code.gates_ifEq, Code.gates, BinOp.gates]
  ring

def equalCode : Code 6 :=
  Code.ifEq (.var 0) (.var 3)
    (Code.ifEq (.var 1) (.var 4) (Code.ifEq (.var 2) (.var 5) 1 0) 0) 0

theorem equalCode_correct (W : Affine (ZMod p)) (P Q : W.Point) :
    equalCode.eval (inputs P Q) = if P = Q then 1 else 0 := by
  have he : P = Q ↔ encode P 0 = encode Q 0 ∧ encode P 1 = encode Q 1 ∧ encode P 2 = encode Q 2 := by
    refine ⟨fun h => by subst Q; simp, ?_⟩
    rintro ⟨h₀, h₁, h₂⟩
    apply encode_injective W
    funext i
    fin_cases i <;> assumption
  simp only [he, ite_and]
  simp [equalCode, Code.eval_ifEq, Code.eval, inputs]

theorem equalCode_gates (w : Nat) : equalCode.gates w = 21 * w := by
  simp [equalCode, Code.gates_ifEq, Code.gates]
  omega

end Signatures.Runtime.EllipticCurveCode
