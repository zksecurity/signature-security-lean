import Signatures.Runtime.Caliper.ListLayout
import Signatures.Runtime.Caliper.ListFoldSetup

/-! Canonical bytes of bounded source lists. Their stored length can be read
directly; a proved singleton permits reading the one represented entry without
assuming a default value or traversing unrelated reserved payload words. -/
namespace Signatures.Runtime.CaliperBackend.BoundedSource.ListBytes
open Caliper Assembly
variable {w : Nat} {A : Type} (entry : Layout w A) (capacity : Nat)
    (countFits : capacity < 2 ^ w) (storageFits : 1 + capacity * entry.representation.encoding.words < 2 ^ w)

def payload (value : (entry.boundedList capacity countFits storageFits).Value) : List (Word w) :=
  entry.representation.encoding.pack (listView entry capacity value).val ++
    List.replicate ((capacity - (listView entry capacity value).val.length) * entry.representation.encoding.words) 0

theorem bytes (value : (entry.boundedList capacity countFits storageFits).Value) :
    (entry.boundedList capacity countFits storageFits).representation.encoding.encode value =
      BitVec.ofNat w value.val.length :: payload entry capacity countFits storageFits value := by
  have length := congrArg List.length (listView_values entry capacity value)
  simp only [List.length_map] at length
  change BitVec.ofNat w (listView entry capacity value).val.length :: _ = _
  unfold payload
  rw [length]

theorem singleton_bytes (value : (entry.boundedList capacity countFits storageFits).Value) (head : entry.Value)
    (single : value.val = [head.val]) :
    (entry.boundedList capacity countFits storageFits).representation.encoding.encode value =
      (1 : Word w) :: (entry.representation.encoding.encode head ++
        List.replicate ((capacity - 1) * entry.representation.encoding.words) 0) := by
  have typed : (listView entry capacity value).val = [head] := by
    apply List.map_injective_iff.mpr Subtype.val_injective
    exact (listView_values entry capacity value).trans single
  change BitVec.ofNat w (listView entry capacity value).val.length ::
    (entry.representation.encoding.pack (listView entry capacity value).val ++ _) = _
  rw [typed]
  simp only [List.length_cons, List.length_nil, Encoding.pack, List.append_nil]
  rfl

theorem read_header (value : (entry.boundedList capacity countFits storageFits).Value)
    (leading suffix : List (Word w)) (before : State w)
    (contents : (before.bufs 0).toList = leading ++
      ((entry.boundedList capacity countFits storageFits).representation.encoding.encode value ++ suffix)) :
    values (reads 0 leading.length 1) before = [BitVec.ofNat w value.val.length] := by
  apply ListFold.reads_block leading [BitVec.ofNat w value.val.length]
    (payload entry capacity countFits storageFits value ++ suffix) before
  simpa only [bytes, List.cons_append, List.singleton_append, List.nil_append, List.append_assoc] using contents

theorem read_singleton (value : (entry.boundedList capacity countFits storageFits).Value) (head : entry.Value)
    (single : value.val = [head.val]) (leading suffix : List (Word w)) (before : State w)
    (contents : (before.bufs 0).toList = leading ++
      ((entry.boundedList capacity countFits storageFits).representation.encoding.encode value ++ suffix)) :
    values (reads 0 (leading.length + 1) entry.representation.encoding.words) before =
      entry.representation.encoding.encode head := by
  have read := ListFold.reads_block (leading ++ [(1 : Word w)]) (entry.representation.encoding.encode head)
    (List.replicate ((capacity - 1) * entry.representation.encoding.words) 0 ++ suffix) before (by
      rw [singleton_bytes entry capacity countFits storageFits value head single] at contents
      simpa only [List.append_assoc, List.singleton_append, List.cons_append, List.nil_append] using contents)
  simpa only [List.length_append, List.length_cons, List.length_nil, Encoding.encode_length] using read

end Signatures.Runtime.CaliperBackend.BoundedSource.ListBytes
