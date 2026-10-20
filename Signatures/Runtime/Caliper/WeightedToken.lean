import Signatures.Runtime.Caliper.WeightedTokenLayout

/-! Constructed extraction for one chronological signing occurrence. The
generator's own output bound supplies admission and preserves the remaining
weighted cache reservation. -/
namespace Signatures.Runtime.CaliperBackend.WeightedToken
open Caliper BoundedSource OracleComp OracleSpec

variable {w : Nat} {Atom : Type} {base : Atom → Type} {key val : Ty Atom} {M G F : Type}
    [DecidableEq (key.Value base)]
    (layout : Layouts w (key.Value base) M G F (val.Value base))
    (zero : layout.accumulation.cache.value.Value)
    (terms : Nat) (termCountFits : terms < 2 ^ w)
    (termStorageFits : 1 + terms * (WeightedRows.term layout.accumulation).representation.encoding.words +
      layout.state.representation.encoding.words < 2 ^ w)
    {generate : M → List (key.Value base × F)}
    (generator : Implementation .unit layout.weighted.message
      (GeneratedWeighted.terms layout.accumulation terms termCountFits termStorageFits) generate)
    (default : layout.accumulation.cache.value.Value)
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    {combine : F × (val.Value base × val.Value base) → val.Value base}
    (update : Implementation .unit layout.accumulation.combine layout.accumulation.cache.value combine)
    {slots : Nat} (updateBuffers : update.program.code.memBound ≤ slots) (reserve : slots + 2 < 2 ^ w)
    {I : Type} {spec : OracleSpec I}

def ready (value : Input layout) : Prop :=
  WeightedCoefficient.valid layout.weighted (generate := generate) (argument layout value)
def denote (source : OracleComp spec layout.accumulation.cache.value.Value) (value : Input layout) :
    OracleComp spec layout.state.Value :=
  WeightedCoefficient.denote layout.weighted zero terms termCountFits termStorageFits generator default
    P comparison correct update updateBuffers reserve source (argument layout value)
def code (port : Interactive.Port w spec) (draw : Interactive.Code w) : Interactive.Code w :=
  .seq (.compute (prepare layout).code)
    (WeightedCoefficient.code layout.weighted zero terms termCountFits termStorageFits generator default
      P comparison correct update updateBuffers reserve port draw)

include generator in
omit [DecidableEq (key.Value base)] in
theorem ready_of_room (remaining : Nat) (value : Input layout)
    (reserved : room layout terms (remaining + 1) value.2) : ready layout (generate := generate) value := by
  have bounded := (generator.preserves value.1.val.1.1 value.1.property.1.1).1
  change (generate value.1.val.1.1).length ≤ terms at bounded
  change value.2.val.2.length + (generate value.1.val.1.1).length ≤ _
  unfold room at reserved
  rw [Nat.mul_add, Nat.mul_one] at reserved
  dsimp only [Layouts.accumulation] at reserved
  omega

theorem cache_growth (source : OracleComp spec layout.accumulation.cache.value.Value)
    (value : Input layout) (admitted : ready layout (generate := generate) value) (answer : layout.state.Value)
    (reached : answer ∈ support (denote layout zero terms termCountFits termStorageFits generator default
      P comparison correct update updateBuffers reserve source value)) :
    answer.val.2.length ≤ value.2.val.2.length + (generate value.1.val.1.1).length :=
  WeightedCoefficient.cache_growth layout.weighted zero terms termCountFits termStorageFits generator default
    P comparison correct update updateBuffers reserve source (argument layout value) admitted answer reached

theorem preserves {source : OracleComp spec layout.accumulation.cache.value.Value}
    (remaining : Nat) (value : Input layout) (reserved : room layout terms (remaining + 1) value.2)
    (answer : layout.state.Value)
    (reached : answer ∈ support (denote layout zero terms termCountFits termStorageFits generator default
      P comparison correct update updateBuffers reserve source value)) :
    room layout terms remaining answer := by
  have admitted := ready_of_room layout terms termCountFits termStorageFits generator remaining value reserved
  have growth := cache_growth layout zero terms termCountFits termStorageFits generator default
    P comparison correct update updateBuffers reserve source value admitted answer reached
  have bounded := (generator.preserves value.1.val.1.1 value.1.property.1.1).1
  change (generate value.1.val.1.1).length ≤ terms at bounded
  unfold room at reserved ⊢
  rw [Nat.mul_add, Nat.mul_one] at reserved
  omega

variable (port : Interactive.Port w spec) {draw : Interactive.Code w}
    {source : OracleComp spec layout.accumulation.cache.value.Value}
    (drawCorrect : Interactive.Refines port .unit layout.accumulation.cache.lookup.unit.representation
      layout.accumulation.cache.value.representation (fun _ => source) draw)

include drawCorrect in
theorem refines : Interactive.RefinesOn (ready layout (generate := generate)) port .unit layout.input
    layout.state.representation
    (denote layout zero terms termCountFits termStorageFits generator default P comparison correct update updateBuffers reserve source)
    (code layout zero terms termCountFits termStorageFits generator default P comparison correct update updateBuffers reserve port draw) := by
  have composed := ((Interactive.Refines.compute port .unit (prepare layout)).on
    (ready layout (generate := generate))).seq
    (WeightedCoefficient.refines layout.weighted zero terms termCountFits termStorageFits generator default
      P comparison correct update updateBuffers reserve port draw drawCorrect) (by
        intro value admitted answer reached
        simp only [support_pure, Set.mem_singleton_iff] at reached
        subst answer
        exact admitted)
  convert composed using 1
  · funext value
    simp only [pure_bind]
    rfl
  · rfl

end Signatures.Runtime.CaliperBackend.WeightedToken
