import Signatures.Runtime.InputCircuit
import Signatures.Runtime.CryptoCircuitExecution

/-! Fixed-width operand layouts for primitive instructions. Variable-length
lists intentionally have no layout here: they require a shared runtime heap. -/

namespace Signatures.Runtime.FixedPorts

open Std.Sat CircuitWires WeierstrassCurve

inductive Layout : Ty CryptoAtom → Type
  | atom (a : CryptoAtom) : Layout (.atom a)
  | unit : Layout .unit
  | bool : Layout .bool
  | nat : Layout .nat
  | pair {a b : Ty CryptoAtom} : Layout a → Layout b → Layout (.pair a b)

def Layout.width (w : Nat) : {t : Ty CryptoAtom} → Layout t → Nat
  | _, .atom .point₁ | _, .atom .point₂ => w + w + w
  | _, .atom _ | _, .nat => w
  | _, .unit => 0
  | _, .bool => 1
  | _, .pair a b => a.width w + b.width w

private def pointIndex (w : Nat) : Fin 3 → Fin w → Fin (w + w + w) :=
  ![fun i => (i.castAdd w).castAdd w,
    fun i => (i.natAdd w).castAdd w,
    fun i => i.natAdd (w + w)]

def Layout.wires {A : Type} [Hashable A] [DecidableEq A] {aig : AIG A} (w : Nat) :
    {t : Ty CryptoAtom} → (layout : Layout t) →
      (Fin (layout.width w) → AIG.Ref aig) → Wires w aig t
  | _, .atom .point₁, f | _, .atom .point₂, f =>
    fun j => InputCircuit.wires (fun i => f (pointIndex w j i))
  | _, .atom .scalar, f | _, .atom .key, f | _, .atom .message, f |
      _, .atom (.fin _), f | _, .nat, f => InputCircuit.wires f
  | _, .unit, _ => ()
  | _, .bool, f => f (0 : Fin 1)
  | _, .pair a b, f =>
    (a.wires w (fun i => f (i.castAdd (b.width w))),
      b.wires w (fun i => f (i.natAdd (a.width w))))

private def pointEncode {p w : Nat} [Fact p.Prime] {W : Affine (ZMod p)} (x : W.Point) :
    Fin (w + w + w) → Bool :=
  Fin.append (Fin.append
    (fun i : Fin w => (BitVec.ofNat w (EllipticCurveCode.encode x 0).val).getLsbD i)
    (fun i : Fin w => (BitVec.ofNat w (EllipticCurveCode.encode x 1).val).getLsbD i))
    (fun i : Fin w => (BitVec.ofNat w (EllipticCurveCode.encode x 2).val).getLsbD i)

private theorem pointEncode_index {p w : Nat} [Fact p.Prime] {W : Affine (ZMod p)}
    (x : W.Point) (j : Fin 3) (i : Fin w) :
    pointEncode x (pointIndex w j i) =
      (BitVec.ofNat w (EllipticCurveCode.encode x j).val).getLsbD i := by
  fin_cases j <;> simp [pointIndex, pointEncode, -Fin.natAdd_eq_addNat]

variable {r p₁ p₂ w : Nat} [Fact p₁.Prime] [Fact p₂.Prime]
  {W₁ : Affine (ZMod p₁)} {W₂ : Affine (ZMod p₂)} {K M : Type}
  (H₁ : AddSubgroup W₁.Point) (H₂ : AddSubgroup W₂.Point)
  (encodeK : K → BitVec w) (encodeM : M → BitVec w)

/-- Semantic specification of the operand bits; not an online encoder for
abstract field/group values. The runtime supplies an already encoded vector. -/
def Layout.encode : {t : Ty CryptoAtom} → (layout : Layout t) →
    t.Value (cryptoBase (ZMod r) H₁ H₂ K M) → Fin (layout.width w) → Bool
  | _, .atom .scalar, x => fun i => (BitVec.ofNat w x.val).getLsbD i
  | _, .atom .point₁, x => pointEncode (x : W₁.Point)
  | _, .atom .point₂, x => pointEncode (x : W₂.Point)
  | _, .atom .key, x => fun i => (encodeK x).getLsbD i
  | _, .atom .message, x => fun i => (encodeM x).getLsbD i
  | _, .atom (.fin _), x => fun i => (BitVec.ofNat w x.val).getLsbD i
  | _, .unit, _ => Fin.elim0
  | _, .bool, x => fun _ => x
  | _, .nat, x => fun i => (BitVec.ofNat w x).getLsbD i
  | _, .pair a b, x => Fin.append
    (a.encode x.1) (b.encode x.2)

theorem Layout.encode_bits {t : Ty CryptoAtom} (layout : Layout t)
    (x : t.Value (cryptoBase (ZMod r) H₁ H₂ K M)) :
    List.ofFn (layout.encode H₁ H₂ encodeK encodeM x) = CryptoCircuit.portBits H₁ H₂ encodeK encodeM x := by
  induction layout with
  | atom a =>
    cases a with
    | scalar | key | message | fin n => rfl
    | point₁ | point₂ =>
      dsimp only [Layout.encode, Layout.width, pointEncode]
      rw [List.ofFn_fin_append, List.ofFn_fin_append]
      rfl
  | unit => rfl
  | bool => simp [Layout.encode, Layout.width, CryptoCircuit.portBits]
  | nat => rfl
  | pair a b iha ihb =>
    dsimp only [Layout.encode, Layout.width, CryptoCircuit.portBits]
    rw [List.ofFn_fin_append, iha, ihb]

theorem Layout.represents {A : Type} [Hashable A] [DecidableEq A] {aig : AIG A}
    {t : Ty CryptoAtom} (layout : Layout t) (refs : Fin (layout.width w) → AIG.Ref aig)
    (assign : A → Bool) (x : t.Value (cryptoBase (ZMod r) H₁ H₂ K M))
    (hb : NaturalRange.ValueBound w x)
    (hx : ∀ i, AIG.denote assign ⟨aig, refs i⟩ = layout.encode H₁ H₂ encodeK encodeM x i) :
    CryptoCircuit.Represents H₁ H₂ encodeK encodeM assign aig (layout.wires w refs) x := by
  have word (f : Fin w → AIG.Ref aig) (v : BitVec w)
      (h : ∀ i, AIG.denote assign ⟨aig, f i⟩ = v.getLsbD i) :
      PrimeFieldCircuit.Represents assign aig (InputCircuit.wires f) v := by
    intro i hi
    rw [InputCircuit.wires_get f ⟨i, hi⟩]
    exact h ⟨i, hi⟩
  induction layout with
  | atom a =>
    cases a with
    | scalar | key | message => exact word _ _ hx
    | fin n => exact ⟨hb, word _ _ hx⟩
    | point₁ | point₂ =>
      intro j
      apply word
      intro i
      exact (hx (pointIndex w j i)).trans (pointEncode_index _ j i)
  | unit => trivial
  | bool => exact hx (0 : Fin 1)
  | nat => exact ⟨hb, word _ _ hx⟩
  | pair a b iha ihb =>
    constructor
    · apply iha _ x.1 hb.1
      intro i
      simpa only [Layout.encode, Fin.append_left] using hx (i.castAdd (b.width w))
    · apply ihb _ x.2 hb.2
      intro i
      simpa only [Layout.encode, Fin.append_right] using hx (i.natAdd (a.width w))

def inputLayout {a b : Ty CryptoAtom} : CryptoOp a b → Layout a
  | .zero | .one | .zero₁ | .zero₂ | .finZero _ => .unit
  | .add | .sub | .mul | .div | .scalarEq => .pair (.atom .scalar) (.atom .scalar)
  | .neg => .atom .scalar
  | .add₁ | .sub₁ | .point₁Eq => .pair (.atom .point₁) (.atom .point₁)
  | .add₂ | .sub₂ | .point₂Eq => .pair (.atom .point₂) (.atom .point₂)
  | .scale₁ => .pair (.atom .scalar) (.atom .point₁)
  | .scale₂ => .pair (.atom .scalar) (.atom .point₂)
  | .keyEq => .pair (.atom .key) (.atom .key)
  | .messageEq => .pair (.atom .message) (.atom .message)
  | .natAdd | .natSub | .natEq | .natLt => .pair .nat .nat
  | .finVal n => .atom (.fin n)
  | .finOfNat _ => .nat

theorem inputWidth_le {a b : Ty CryptoAtom} (op : CryptoOp a b) :
    (inputLayout op).width w ≤ 6*w := by
  cases op <;> simp [inputLayout, Layout.width] <;> omega

def outputLayout {a b : Ty CryptoAtom} : CryptoOp a b → Layout b
  | .zero | .one | .add | .sub | .mul | .div | .neg => .atom .scalar
  | .zero₁ | .add₁ | .sub₁ | .scale₁ => .atom .point₁
  | .zero₂ | .add₂ | .sub₂ | .scale₂ => .atom .point₂
  | .scalarEq | .point₁Eq | .point₂Eq | .keyEq | .messageEq | .natEq | .natLt => .bool
  | .natAdd | .natSub | .finVal _ => .nat
  | .finZero n | .finOfNat n => .atom (.fin n)

theorem outputLayout_width {a b : Ty CryptoAtom} (op : CryptoOp a b) :
    (outputLayout op).width w = CryptoCircuit.outputWidth w op := by
  cases op <;> simp [outputLayout, Layout.width, CryptoCircuit.outputWidth] <;> omega

def Layout.ports {t : Ty CryptoAtom} (layout : Layout t) (w : Nat) :
    Compiled w (AIG.empty : AIG (Fin (layout.width w))) t :=
  let inputs := InputCircuit.build id (AIG.empty : AIG (Fin (layout.width w)))
  ⟨inputs.result.aig,
    layout.wires w (fun i => inputs.result.vec.get i i.isLt), inputs.extension⟩

theorem Layout.ports_size {t : Ty CryptoAtom} (layout : Layout t) (w : Nat) :
    (layout.ports w).graph.decls.size = 1 + layout.width w := by
  simp [ports, InputCircuit.build_size, AIG.empty]

theorem Layout.ports_correct {t : Ty CryptoAtom} (layout : Layout t)
    (input : Vector Bool (layout.width w))
    (x : t.Value (cryptoBase (ZMod r) H₁ H₂ K M)) (hb : NaturalRange.ValueBound w x)
    (hx : ∀ i, input[i] = layout.encode H₁ H₂ encodeK encodeM x i) :
    CryptoCircuit.Represents H₁ H₂ encodeK encodeM (fun i => input[i])
      (layout.ports w).graph (layout.ports w).refs x := by
  apply layout.represents H₁ H₂ encodeK encodeM _ _ x hb
  intro i
  exact (InputCircuit.build_correct id AIG.empty (fun i => input[i]) i).trans (hx i)

end Signatures.Runtime.FixedPorts
