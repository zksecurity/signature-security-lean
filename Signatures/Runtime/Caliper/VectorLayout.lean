import Signatures.Runtime.Caliper.ListFoldSetup
import Signatures.Runtime.Caliper.ListLayout

/-! Fixed scalar vectors retain the original function type. Their encoding is
the concatenation of coordinate encodings, with no enumerated scalar domain.
The dimension controls stored input size and every coordinate's read offset. -/
namespace Signatures.Runtime.CaliperBackend.BoundedSource
open Caliper
variable {w : Nat} {A : Type} (entry : Layout w A)

private def vectorZeroView : {value : Fin 0 → A // ∀ i, entry.valid (value i)} ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨Fin.elim0, fun i => Fin.elim0 i⟩
  left_inv value := by
    apply Subtype.ext
    funext i
    exact Fin.elim0 i
  right_inv _ := rfl

private def vectorSuccView (n : Nat) :
    {value : Fin (n + 1) → A // ∀ i, entry.valid (value i)} ≃
      entry.Value × {value : Fin n → A // ∀ i, entry.valid (value i)} where
  toFun value := (⟨value.val 0, value.property 0⟩, ⟨fun i => value.val i.succ, fun i => value.property i.succ⟩)
  invFun value := ⟨Fin.cases value.1.val value.2.val, Fin.cases value.1.property value.2.property⟩
  left_inv value := by
    apply Subtype.ext
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  right_inv _ := rfl

def vectorEncoding : (n : Nat) → Encoding w {value : Fin n → A // ∀ i, entry.valid (value i)}
  | 0 => (Encoding.unit w).transport (vectorZeroView entry)
  | n + 1 => (entry.representation.encoding.prod (vectorEncoding n)).transport (vectorSuccView entry n)

theorem vectorEncoding_words (n : Nat) :
    (vectorEncoding entry n).words = n * entry.representation.encoding.words := by
  induction n with
  | zero => simp [vectorEncoding, Encoding.transport, Encoding.unit, Encoding.checked]
  | succ n ih =>
    change entry.representation.encoding.words + (vectorEncoding entry n).words = _
    rw [ih, Nat.add_mul]
    omega

def Layout.vector (n : Nat) (fits : n * entry.representation.encoding.words < 2 ^ w) :
    Layout w (Fin n → A) where
  valid value := ∀ i, entry.valid (value i)
  representation := ⟨vectorEncoding entry n, by rw [vectorEncoding_words]; exact fits⟩

theorem vectorEncoding_encode (n : Nat) (value : {value : Fin n → A // ∀ i, entry.valid (value i)}) :
    (vectorEncoding entry n).encode value =
      (List.ofFn (fun i => entry.representation.encoding.encode ⟨value.val i, value.property i⟩)).flatten := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change entry.representation.encoding.encode ⟨value.val 0, value.property 0⟩ ++
      (vectorEncoding entry n).encode ⟨fun i => value.val i.succ, fun i => value.property i.succ⟩ = _
    rw [ih]
    simp only [List.ofFn_succ, List.flatten_cons]

/-- Read exactly one coordinate from a represented vector inside an arbitrary
stored frame. The surrounding prefix and suffix are never interpreted. -/
theorem vectorEncoding_read (n : Nat) (value : {value : Fin n → A // ∀ i, entry.valid (value i)})
    (leading trailing : List (Word w)) (before : State w)
    (contents : (before.bufs 0).toList = leading ++ (vectorEncoding entry n).encode value ++ trailing)
    (i : Fin n) :
    Assembly.values (Assembly.reads 0 (leading.length + i.val * entry.representation.encoding.words)
      entry.representation.encoding.words) before =
        entry.representation.encoding.encode ⟨value.val i, value.property i⟩ := by
  induction n generalizing leading with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    let first := entry.representation.encoding.encode ⟨value.val 0, value.property 0⟩
    let rest := (vectorEncoding entry n).encode ⟨fun j => value.val j.succ, fun j => value.property j.succ⟩
    change (before.bufs 0).toList = leading ++ (first ++ rest) ++ trailing at contents
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa [first, Encoding.encode_length] using ListFold.reads_block leading first (rest ++ trailing) before
        (by simpa [List.append_assoc] using contents)
    · have tailRead := ih ⟨fun j => value.val j.succ, fun j => value.property j.succ⟩
        (leading ++ first) (by simpa [List.append_assoc, rest] using contents) j
      simpa [first, List.length_append, Encoding.encode_length, Fin.val_succ, Nat.add_mul,
        Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using tailRead

theorem boundedList_encode_ofFn (n : Nat) (countFits : n < 2 ^ w)
    (storageFits : 1 + n * entry.representation.encoding.words < 2 ^ w)
    (value : Fin n → entry.Value) :
    (entry.boundedList n countFits storageFits).representation.encoding.encode
        ⟨List.ofFn (fun i => (value i).val), by
          refine ⟨by simp, ?_⟩
          intro item member
          obtain ⟨i, rfl⟩ := List.mem_ofFn.mp member
          exact (value i).property⟩ =
      BitVec.ofNat w n :: (List.ofFn (fun i => entry.representation.encoding.encode (value i))).flatten := by
  have represented :
      (listView entry n ⟨List.ofFn (fun i => (value i).val), by
        refine ⟨by simp, ?_⟩
        intro item member
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp member
        exact (value i).property⟩).val = List.ofFn value := by
    apply List.map_injective_iff.mpr Subtype.val_injective
    rw [listView_values, List.map_ofFn]
    rfl
  dsimp only [Layout.boundedList, Representation.transport, Encoding.transport]
  change BitVec.ofNat w _ :: (_ ++ List.replicate _ 0) = _
  rw [represented]
  simp only [List.length_ofFn, Nat.sub_self, Nat.zero_mul, List.replicate_zero, List.append_nil]
  congr 1
  clear represented countFits storageFits
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [List.ofFn_succ, Encoding.pack, List.flatten_cons]
    rw [ih]

end Signatures.Runtime.CaliperBackend.BoundedSource
