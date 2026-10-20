import Signatures.Runtime.Caliper.WeightedRowsLayout

/-! Executed lazy evaluation of weighted terms. Only the local accumulator
update and sampler are supplied; traversal, lookup, copying and cache storage
come from the constructed row fold. No index-domain enumeration occurs. -/
namespace Signatures.Runtime.CaliperBackend.WeightedRows
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat} {Atom : Type} {base : Atom → Type} {key val : Ty Atom} {F : Type}
    [DecidableEq (key.Value base)]
    (layout : CacheAccumulate.Layouts w (key.Value base) F (val.Value base))
    (default : layout.cache.value.Value)
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    {combine : F × (val.Value base × val.Value base) → val.Value base}
    (update : Implementation .unit layout.combine layout.cache.value combine)
    {slots : Nat} (updateBuffers : update.program.code.memBound ≤ slots) (reserve : slots + 2 < 2 ^ w)
    {I : Type} {spec : OracleSpec I}

def valid {capacity : Nat} (value : Input layout capacity) : Prop :=
  value.2.val.2.length + value.1.val.length ≤ layout.cache.capacityPred + 1

omit [DecidableEq (key.Value base)] in
theorem view_valid {capacity : Nat} (value : Input layout capacity) :
    RowFold.valid (base := base) (key := key) (val := val) (rows layout) (view layout value) =
      valid layout value := by
  change (_ + (value.1.val.map (rowView layout)).length ≤ _) = _
  rw [List.length_map]
  rfl

def code (capacity : Nat) (port : Interactive.Port w spec) (draw : Interactive.Code w) : Interactive.Code w :=
  RowFold.code (base := base) (key := key) (val := val) (rows layout) default P comparison correct
    update updateBuffers reserve capacity port draw

def denote (source : OracleComp spec layout.cache.value.Value) {capacity : Nat}
    (value : Input layout capacity) : OracleComp spec (rows layout).state.Value :=
  RowFold.denote (base := base) (key := key) (val := val) (rows layout) default P comparison correct
    update updateBuffers reserve source (view layout value)

/-- The original ordered weighted fold, including its final lazy cache. -/
def sourceStep (sample : OracleComp spec (val.Value base))
    (state : val.Value base × List (key.Value base × val.Value base)) (entry : key.Value base × F) :
    OracleComp spec (val.Value base × List (key.Value base × val.Value base)) :=
  (fun result => (combine (entry.2, result.1, state.1), result.2)) <$>
    (QueryImpl.ListCache.handler (fun _ => sample) entry.1).run state.2

theorem listCache (source : OracleComp spec layout.cache.value.Value) {capacity : Nat}
    (value : Input layout capacity) (admitted : valid layout value) :
    Subtype.val <$> denote layout default P comparison correct update updateBuffers reserve source value =
      (value.1.val.map Subtype.val).foldlM (sourceStep (combine := combine) (Subtype.val <$> source)) value.2.val := by
  have result := RowFold.listCache (base := base) (key := key) (val := val) (rows layout)
    default P comparison correct update updateBuffers reserve source (view layout value)
    (by simpa only [view_valid] using admitted)
  simp only [view, List.foldlM_map] at result
  simp only [List.foldlM_map]
  exact result

theorem cache_growth (source : OracleComp spec layout.cache.value.Value) {capacity : Nat}
    (value : Input layout capacity) (admitted : valid layout value)
    (answer : (rows layout).state.Value)
    (reached : answer ∈ support (denote layout default P comparison correct update updateBuffers reserve source value)) :
    answer.val.2.length ≤ value.2.val.2.length + value.1.val.length := by
  have growth := RowFold.cache_growth (base := base) (key := key) (val := val) (rows layout)
    default P comparison correct update updateBuffers reserve source (view layout value)
    (by simpa only [view_valid] using admitted) answer reached
  simpa only [view, List.length_map] using growth

theorem remaining_room (source : OracleComp spec layout.cache.value.Value) {capacity : Nat}
    (value : Input layout capacity) (remaining : Nat)
    (reserved : value.2.val.2.length + value.1.val.length + remaining ≤ layout.cache.capacityPred + 1)
    (answer : (rows layout).state.Value)
    (reached : answer ∈ support (denote layout default P comparison correct update updateBuffers reserve source value)) :
    answer.val.2.length + remaining ≤ layout.cache.capacityPred + 1 := by
  have growth := cache_growth layout default P comparison correct update updateBuffers reserve source
    value (by unfold valid; omega) answer reached
  omega

variable (port : Interactive.Port w spec) {source : OracleComp spec layout.cache.value.Value}
    {draw : Interactive.Code w}
    (drawCorrect : Interactive.Refines port .unit layout.cache.lookup.unit.representation
      layout.cache.value.representation (fun _ => source) draw)
    (capacity : Nat) (countFits : capacity < 2 ^ w)
    (storageFits : 1 + capacity * (term layout).representation.encoding.words +
      (rows layout).state.representation.encoding.words < 2 ^ w)

include drawCorrect in
theorem refines :
    Interactive.RefinesOn (valid layout) port .unit (input layout capacity countFits storageFits)
      (rows layout).state.representation (denote layout default P comparison correct update updateBuffers reserve source)
      (code layout default P comparison correct update updateBuffers reserve capacity port draw) := by
  intro tape value admitted before holds
  have refined := RowFold.refines (base := base) (key := key) (val := val) (rows layout)
    default P comparison correct update updateBuffers reserve port drawCorrect capacity countFits
    (by simpa only [row_words] using storageFits)
  exact refined tape (view layout value) ((view_valid layout value).mpr admitted) before
    ⟨holds.1, holds.2.1.trans (input_bytes layout capacity countFits storageFits value).symm, holds.2.2⟩

include drawCorrect in
theorem time_bound {drawTime updateTime updateWords : Nat}
    (drawBound : Interactive.TimeBound port .unit layout.cache.lookup.unit.representation draw drawTime)
    (updateBound : update.BoundedBy updateTime updateWords) :
    Interactive.TimeBoundOn (valid layout) port .unit (input layout capacity countFits storageFits)
      (code layout default P comparison correct update updateBuffers reserve capacity port draw)
      (RowFold.timeBudget (rows layout) capacity drawTime updateTime) := by
  intro tape value admitted before holds
  have bounded := RowFold.time_bound (base := base) (key := key) (val := val) (rows layout)
    default P comparison correct update updateBuffers reserve port drawCorrect capacity countFits
    (by simpa only [row_words] using storageFits) drawBound updateBound
  exact bounded tape (view layout value) ((view_valid layout value).mpr admitted) before
    ⟨holds.1, holds.2.1.trans (input_bytes layout capacity countFits storageFits value).symm, holds.2.2⟩

end Signatures.Runtime.CaliperBackend.WeightedRows
