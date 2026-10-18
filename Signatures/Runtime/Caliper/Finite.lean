import Signatures.Runtime.Caliper.Natural

/-! Finite-counter conversions for the original source instructions. Modulo
conversion executes word division after constructing its operands. When the
modulus is the entire word domain, bounded input already has the required bytes. -/

namespace Signatures.Runtime.CaliperBackend.BoundedSource.Finite

open Caliper Assembly

variable {w : Nat} {A : Type}

def layout (bound : Nat) (hw : 16 < 2 ^ w) (fits : bound + 1 ≤ 2 ^ w) : Layout w (Fin (bound + 1)) :=
  Layout.all (Representation.fin w (bound + 1) (width_pos hw) fits)

def constant (cost : CostModel) (allocation : 1 ≤ cost.allocPerWord) (input : Layout w A)
    (bound : Nat) (value : Fin (bound + 1)) (hw : 16 < 2 ^ w) (fits : bound + 1 ≤ 2 ^ w) :
    Implementation cost input (layout bound hw fits) (fun _ => value) where
  preserves _ _ := trivial
  program := (Natural.constant cost allocation input (bound + 1) value.val hw fits value.isLt).program.viewOutput _ _ (fun _ => rfl)

def value (cost : CostModel) (bound : Nat) (hw : 16 < 2 ^ w) (fits : bound + 1 ≤ 2 ^ w) :
    Implementation cost (layout bound hw fits) (Layout.counter w (bound + 1) (width_pos hw) fits) Fin.val where
  preserves value _ := value.isLt
  program := (Realizer.identity (cost := cost) (width_pos hw) (layout bound hw fits).representation).viewOutput _ _ (fun _ => rfl)

def operands (cost : CostModel) (allocation : 1 ≤ cost.allocPerWord)
    (inputBound modulus : Nat) (hw : 16 < 2 ^ w) (inputFits : inputBound ≤ 2 ^ w) :
    Realizer cost (Layout.counter w inputBound (width_pos hw) inputFits).representation (WordBinary.pair w hw)
      (fun value => (BitVec.ofNat w value.val, BitVec.ofNat w modulus)) :=
  Assembly.realizer cost allocation _ _ _ [.read 0 0, .literal (BitVec.ofNat w modulus)] hw rfl
    (by
      intro operand member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> simp [Operand.NamesFit])
    (by
      intro value state represented operand member
      have size := represented_size _ represented
      change (state.bufs 0).size = 1 at size
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> simp [Operand.Valid, size])
    (by
      intro value state represented
      have bytes : state.bufs 0 = #[BitVec.ofNat w value.val] := by
        have array := congrArg List.toArray represented.2.1
        simpa [Layout.counter, Representation.transport, Encoding.transport, Representation.fin, Encoding.fin, Encoding.checked] using array
      simp [values, Operand.value, bytes, WordBinary.pair, wordRepresentation, wordEncoding, Representation.prod,
        Encoding.prod, Encoding.checked])

def ofNat (cost : CostModel) (allocation : 1 ≤ cost.allocPerWord)
    (inputBound bound : Nat) (hw : 16 < 2 ^ w) (inputFits : inputBound ≤ 2 ^ w) (outputFits : bound + 1 ≤ 2 ^ w) :
    Implementation cost (Layout.counter w inputBound (width_pos hw) inputFits) (layout bound hw outputFits)
      (fun value => ⟨value % (bound + 1), Nat.mod_lt _ (Nat.zero_lt_succ bound)⟩) where
  preserves _ _ := trivial
  program := if entire : bound + 1 = 2 ^ w then
      (Realizer.identity (cost := cost) (width_pos hw) (Layout.counter w inputBound (width_pos hw) inputFits).representation).viewOutput _ _ (by
        intro value
        change [BitVec.ofNat w (value.val % (bound + 1))] = [BitVec.ofNat w value.val]
        rw [Nat.mod_eq_of_lt (show value.val < bound + 1 by rw [entire]; exact value.property.trans_le inputFits)])
    else
      ((operands cost allocation inputBound (bound + 1) hw inputFits).then
        (WordBinary.realizer cost .umod hw)).viewOutput _ _ (by
          intro value
          have modulusFits : bound + 1 < 2 ^ w := lt_of_le_of_ne outputFits entire
          change [BitVec.ofNat w (value.val % (bound + 1))] = [BitVec.ofNat w value.val % BitVec.ofNat w (bound + 1)]
          simp [BitVec.umod_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (value.property.trans_le inputFits), Nat.mod_eq_of_lt modulusFits])

end Signatures.Runtime.CaliperBackend.BoundedSource.Finite
