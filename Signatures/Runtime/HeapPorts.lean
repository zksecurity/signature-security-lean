import Signatures.Runtime.TypedHeap
import Signatures.Runtime.FixedPorts

/-! Loading fixed primitive operands from the shared bit heap. Product inputs
follow links; leaf bits are decoded, and concatenation is charged. No semantic
field/group operation or semantic-to-bit conversion runs in this loader. -/

namespace Signatures.Runtime.SharedHeap

open HeapBits FixedPorts WeierstrassCurve

def readWord (memory : List Bool) (addr : Address) : Run (Option (List Bool)) :=
  let node := read addr memory
  ⟨match node.value with | some (.word bits) => some bits | _ => none, node.steps + 1⟩

def loadPorts : {t : Ty CryptoAtom} → Layout t → List Bool → Address → Run (Option (List Bool))
  | _, .atom _, memory, addr | _, .unit, memory, addr |
      _, .bool, memory, addr | _, .nat, memory, addr => readWord memory addr
  | _, .pair a b, memory, addr =>
    let node := read addr memory
    match node.value with
    | some (.pair left right) =>
      let lhs := loadPorts a memory left
      match lhs.value with
      | none => ⟨none, node.steps + lhs.steps + 2⟩
      | some xs =>
        let rhs := loadPorts b memory right
        match rhs.value with
        | none => ⟨none, node.steps + lhs.steps + rhs.steps + 3⟩
        | some ys =>
          let bits := HeapBits.append xs ys
          ⟨some bits.value, node.steps + lhs.steps + rhs.steps + bits.steps + 4⟩
    | _ => ⟨none, node.steps + 1⟩

def portNodes : {t : Ty CryptoAtom} → Layout t → Nat
  | _, .pair a b => 1 + portNodes a + portNodes b
  | _, _ => 1

variable {r p₁ p₂ w : Nat} [Fact p₁.Prime] [Fact p₂.Prime]
  {W₁ : Affine (ZMod p₁)} {W₂ : Affine (ZMod p₂)} {K M : Type}
  (H₁ : AddSubgroup W₁.Point) (H₂ : AddSubgroup W₂.Point)
  (encodeK : K → BitVec w) (encodeM : M → BitVec w)

def atomRep (a : CryptoAtom) (bits : List Bool) (x : cryptoBase (ZMod r) H₁ H₂ K M a) : Prop :=
  bits = CryptoCircuit.portBits H₁ H₂ encodeK encodeM (t := .atom a) x ∧
    NaturalRange.ValueBound w (t := .atom a) x

theorem loadPorts_value {heap : List Node} {t : Ty CryptoAtom} (layout : Layout t)
    (addr : Address) (x : t.Value (cryptoBase (ZMod r) H₁ H₂ K M))
    (hx : Represents w (atomRep H₁ H₂ encodeK encodeM) heap t addr x) :
    (loadPorts layout (tape heap) addr).value = some (CryptoCircuit.portBits H₁ H₂ encodeK encodeM x) := by
  induction layout generalizing addr with
  | atom a =>
    cases hx with
    | atom h hl => simp only [loadPorts, readWord, read_value, h]; exact congrArg some hl.1
  | unit => cases hx; simp [loadPorts, readWord, read_value, *, CryptoCircuit.portBits]
  | bool => cases hx; simp [loadPorts, readWord, read_value, *, CryptoCircuit.portBits]
  | nat => cases hx; simp [loadPorts, readWord, read_value, *, CryptoCircuit.portBits, natBits]; rfl
  | pair a b iha ihb =>
    cases hx with
    | pair h hl hr =>
      simp only [loadPorts, read_value, h, iha _ _ hl, ihb _ _ hr, append_value, CryptoCircuit.portBits]

theorem represents_range {heap : List Node} {t : Ty CryptoAtom} {addr : Address}
    {x : t.Value (cryptoBase (ZMod r) H₁ H₂ K M)}
    (hx : Represents w (atomRep H₁ H₂ encodeK encodeM) heap t addr x) :
    NaturalRange.ValueBound w x := by
  induction hx with
  | atom _ h => exact h.2
  | unit | bool => trivial
  | nat _ hn => exact hn
  | pair _ _ _ ihl ihr => exact ⟨ihl, ihr⟩
  | nil => simp [NaturalRange.ValueBound]
  | cons _ _ _ ihh iht =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ihh
    · exact iht x hx

theorem portBits_length {t : Ty CryptoAtom} (layout : Layout t)
    (x : t.Value (cryptoBase (ZMod r) H₁ H₂ K M)) :
    (CryptoCircuit.portBits H₁ H₂ encodeK encodeM x).length = layout.width w := by
  rw [← layout.encode_bits H₁ H₂ encodeK encodeM x, List.length_ofFn]

theorem loadPorts_steps {heap : List Node} {t : Ty CryptoAtom} (layout : Layout t)
    (addr : Address) (x : t.Value (cryptoBase (ZMod r) H₁ H₂ K M))
    (hx : Represents w (atomRep H₁ H₂ encodeK encodeM) heap t addr x) :
    (loadPorts layout (tape heap) addr).steps ≤ portNodes layout *
      (3*(tape heap).length + 7*(heap.length+1) + 2*layout.width w + 5) := by
  induction layout generalizing addr with
  | atom a | unit | bool | nat =>
    have h := read_steps heap addr
    simp only [loadPorts, readWord, portNodes, Nat.one_mul]
    omega
  | pair a b iha ihb =>
    cases hx with
    | pair h hl hr =>
      rename_i left right x y
      have hlc := loadPorts_value H₁ H₂ encodeK encodeM a _ _ hl
      have hrc := loadPorts_value H₁ H₂ encodeK encodeM b _ _ hr
      have hls := iha _ _ hl
      have hrs := ihb _ _ hr
      have hn := read_steps heap addr
      have hlen := portBits_length H₁ H₂ encodeK encodeM a x
      simp only [loadPorts, read_value, h, hlc, hrc, append_steps,
        portNodes, Layout.width, hlen]
      nlinarith

theorem input_portNodes {a b : Ty CryptoAtom} (op : CryptoOp a b) : portNodes (inputLayout op) ≤ 3 := by
  cases op <;> simp [inputLayout, portNodes]

end Signatures.Runtime.SharedHeap
