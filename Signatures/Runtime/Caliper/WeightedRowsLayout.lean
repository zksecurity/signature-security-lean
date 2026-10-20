import Signatures.Runtime.Caliper.RowFoldMemory
import Signatures.Runtime.Caliper.RowFoldPostcondition

/-! Weighted terms use the existing executed cache fold without storing a
point. The unit component in its mathematical row has zero words. The input
view preserves the complete encoding, including list length and padding. -/
namespace Signatures.Runtime.CaliperBackend.WeightedRows
open Caliper BoundedSource
variable {w : Nat} {K F R : Type} (layout : CacheAccumulate.Layouts w K F R)

def rows : RowRequest.Layouts w K Unit F R where
  accumulation := layout
  point := DataImplementation.unitLayout w
  storageFits := by
    change 16 * (layout.width + 0) < 2 ^ w
    rw [Nat.add_zero]
    exact layout.storageFits

def term : Layout w (K × F) := layout.cache.key.prod layout.coefficient
  (layout.fits_of_le (by
    dsimp only [CacheAccumulate.Layouts.width]
    rw [CacheAccumulate.Layouts.cache_width]
    omega))

def rowView (value : (term layout).Value) : (rows layout).row.Value :=
  ⟨((value.val.1, ()), value.val.2), ⟨value.property.1, trivial⟩, value.property.2⟩

theorem row_words : (rows layout).row.representation.encoding.words =
    (term layout).representation.encoding.words := by
  change (layout.cache.key.representation.encoding.words + 0) +
    layout.coefficient.representation.encoding.words = _
  rw [Nat.add_zero]
  rfl

theorem row_bytes (value : (term layout).Value) :
    (rows layout).row.representation.encoding.encode (rowView layout value) =
      (term layout).representation.encoding.encode value := by
  change (_ ++ []) ++ _ = _ ++ _
  rw [List.append_nil]
  rfl

theorem pack_bytes (values : List (term layout).Value) :
    (rows layout).row.representation.encoding.pack (values.map (rowView layout)) =
      (term layout).representation.encoding.pack values := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.map_cons, Encoding.pack, row_bytes, ih]

abbrev Input (capacity : Nat) :=
  BoundedList (term layout).Value capacity × (rows layout).state.Value

def input (capacity : Nat) (countFits : capacity < 2 ^ w)
    (storageFits : 1 + capacity * (term layout).representation.encoding.words +
      (rows layout).state.representation.encoding.words < 2 ^ w) :
    Representation w (Input layout capacity) :=
  InteractiveFold.frame (term layout).representation (rows layout).state.representation
    capacity countFits storageFits

def view {capacity : Nat} (value : Input layout capacity) :
    BoundedList (rows layout).row.Value capacity × (rows layout).state.Value :=
  (⟨value.1.val.map (rowView layout), by simpa using value.1.property⟩, value.2)

theorem input_bytes (capacity : Nat) (countFits : capacity < 2 ^ w)
    (storageFits : 1 + capacity * (term layout).representation.encoding.words +
      (rows layout).state.representation.encoding.words < 2 ^ w)
    (value : Input layout capacity) :
    (InteractiveFold.frame (rows layout).row.representation (rows layout).state.representation
      capacity countFits (by simpa only [row_words] using storageFits)).encoding.encode (view layout value) =
      (input layout capacity countFits storageFits).encoding.encode value := by
  change (BitVec.ofNat w (value.1.val.map (rowView layout)).length ::
    ((rows layout).row.representation.encoding.pack (value.1.val.map (rowView layout)) ++
      List.replicate ((capacity - (value.1.val.map (rowView layout)).length) *
        (rows layout).row.representation.encoding.words) 0)) ++ _ = _
  rw [List.length_map, pack_bytes, row_words]
  rfl

end Signatures.Runtime.CaliperBackend.WeightedRows
