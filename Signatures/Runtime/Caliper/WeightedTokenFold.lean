import Signatures.Runtime.Caliper.WeightedTokenBounds

/-! Executed streaming extraction across weighted transcript rows. Each body
generates its own terms; the outer loop stores and charges only its row tail. -/
namespace Signatures.Runtime.CaliperBackend.WeightedTokenFold
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat} {Atom : Type} {base : Atom → Type} {key val : Ty Atom} {M G F : Type}
    [DecidableEq (key.Value base)]
    (layout : WeightedToken.Layouts w (key.Value base) M G F (val.Value base))
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

abbrev Input (capacity : Nat) := BoundedList layout.row.Value capacity × layout.state.Value
def input (capacity : Nat) (countFits : capacity < 2 ^ w)
    (storageFits : 1 + capacity * layout.row.representation.encoding.words + layout.state.representation.encoding.words < 2 ^ w) :
    Representation w (Input layout capacity) :=
  InteractiveFold.frame layout.row.representation layout.state.representation capacity countFits storageFits
def valid {capacity : Nat} (value : Input layout capacity) : Prop :=
  WeightedToken.room layout terms value.1.val.length value.2
def code (capacity : Nat) (port : Interactive.Port w spec) (draw : Interactive.Code w) : Interactive.Code w :=
  let body := WeightedToken.code layout zero terms termCountFits termStorageFits generator default P comparison correct update updateBuffers reserve port draw
  InteractiveFold.code body (Interactive.savedBuffer port body)
    layout.row.representation.encoding.words layout.state.representation.encoding.words capacity
def denote (source : OracleComp spec layout.accumulation.cache.value.Value) {capacity : Nat}
    (value : Input layout capacity) : OracleComp spec layout.state.Value :=
  InteractiveFold.denote (WeightedToken.denote layout zero terms termCountFits termStorageFits generator default
    P comparison correct update updateBuffers reserve source) value
def timeBudget (capacity generatorTime drawTime updateTime : Nat) :=
  InteractiveFold.timeBudget layout.row.representation.encoding.words layout.state.representation.encoding.words capacity
    (WeightedToken.timeBudget layout terms termCountFits termStorageFits generatorTime drawTime updateTime)
def codeBudget (capacity generatorWords drawWords updateWords : Nat) :=
  InteractiveFold.codeBudget layout.row.representation.encoding.words layout.state.representation.encoding.words capacity
    (WeightedToken.codeBudget layout terms termCountFits termStorageFits generatorWords drawWords updateWords)

variable (port : Interactive.Port w spec) {source : OracleComp spec layout.accumulation.cache.value.Value}
    {draw : Interactive.Code w}
    (drawCorrect : Interactive.Refines port .unit layout.accumulation.cache.lookup.unit.representation
      layout.accumulation.cache.value.representation (fun _ => source) draw)
    (capacity : Nat) (countFits : capacity < 2 ^ w)
    (storageFits : 1 + capacity * layout.row.representation.encoding.words + layout.state.representation.encoding.words < 2 ^ w)

include drawCorrect in
theorem refines : Interactive.RefinesOn (valid layout terms) port .unit (input layout capacity countFits storageFits)
    layout.state.representation
    (denote layout zero terms termCountFits termStorageFits generator default P comparison correct update updateBuffers reserve source)
    (code layout zero terms termCountFits termStorageFits generator default P comparison correct update updateBuffers reserve capacity port draw) :=
  InteractiveFold.refines layout.row.representation layout.state.representation layout.accumulation.cache.wordFits
    layout.input.fits port (WeightedToken.room layout terms)
    (fun remaining tape value valid before holds =>
      WeightedToken.refines layout zero terms termCountFits termStorageFits generator default P comparison correct update updateBuffers reserve port drawCorrect
        tape value (WeightedToken.ready_of_room layout terms termCountFits termStorageFits generator remaining value valid) before holds)
    (WeightedToken.preserves layout zero terms termCountFits termStorageFits generator default P comparison correct update updateBuffers reserve)
    capacity countFits storageFits

include drawCorrect in
theorem time_bound {generatorTime generatorWords drawTime updateTime updateWords : Nat}
    (generatorBound : generator.BoundedBy generatorTime generatorWords)
    (drawBound : Interactive.TimeBound port .unit layout.accumulation.cache.lookup.unit.representation draw drawTime)
    (updateBound : update.BoundedBy updateTime updateWords) :
    Interactive.TimeBoundOn (valid layout terms) port .unit (input layout capacity countFits storageFits)
      (code layout zero terms termCountFits termStorageFits generator default P comparison correct update updateBuffers reserve capacity port draw)
      (timeBudget layout terms termCountFits termStorageFits capacity generatorTime drawTime updateTime) :=
  InteractiveFold.time_bound layout.row.representation layout.state.representation layout.accumulation.cache.wordFits
    layout.input.fits port (WeightedToken.room layout terms)
    (fun remaining tape value valid before holds =>
      WeightedToken.refines layout zero terms termCountFits termStorageFits generator default P comparison correct update updateBuffers reserve port drawCorrect
        tape value (WeightedToken.ready_of_room layout terms termCountFits termStorageFits generator remaining value valid) before holds)
    (WeightedToken.preserves layout zero terms termCountFits termStorageFits generator default P comparison correct update updateBuffers reserve)
    (fun remaining tape value valid before holds finished reached =>
      WeightedToken.time_bound layout zero terms termCountFits termStorageFits generator default P comparison correct update updateBuffers reserve
        port draw drawCorrect generatorBound drawBound updateBound
        tape value (WeightedToken.ready_of_room layout terms termCountFits termStorageFits generator remaining value valid) before holds finished reached)
    capacity countFits storageFits

theorem code_bound (draw : Interactive.Code w) {generatorTime generatorWords drawWords updateTime updateWords : Nat}
    (generatorBound : generator.BoundedBy generatorTime generatorWords)
    (drawBound : (draw.lower port).descriptionWords ≤ drawWords) (updateBound : update.BoundedBy updateTime updateWords) :
    ((code layout zero terms termCountFits termStorageFits generator default P comparison correct update updateBuffers reserve capacity port draw).lower port).descriptionWords ≤
      codeBudget layout terms termCountFits termStorageFits capacity generatorWords drawWords updateWords :=
  InteractiveFold.code_bound port _ _ _ capacity
    (WeightedToken.code_bound layout zero terms termCountFits termStorageFits generator default P comparison correct update updateBuffers reserve
      port draw generatorBound drawBound updateBound)

theorem names (draw : Interactive.Code w) {generatorNames drawNames updateNames : Nat}
    (generatorBound : NamesAccounted generator.program.code generatorNames)
    (drawBound : WordIO.NamesBound (draw.lower port) drawNames) (updateBound : NamesAccounted update.program.code updateNames) :
    WordIO.NamesAccounted ((code layout zero terms termCountFits termStorageFits generator default P comparison correct update updateBuffers reserve capacity port draw).lower port)
      (max generatorNames (max (max 5 drawNames) updateNames)) :=
  InteractiveFold.names port _ _ _ capacity
    (WeightedToken.names layout zero terms termCountFits termStorageFits generator default P comparison correct update updateBuffers reserve
      port draw generatorBound drawBound updateBound)

include countFits storageFits in
theorem descriptionFits (draw : Interactive.Code w) {generatorSlots drawSlots : Nat}
    (generatorBound : generator.program.code.memBound ≤ generatorSlots) (generatorReserve : generatorSlots + 2 < 2 ^ w)
    (drawFits : (draw.lower port).DescriptionFits)
    (drawBound : WordIO.NamesBound (draw.lower port) drawSlots) (drawReserve : drawSlots + 4 < 2 ^ w)
    (updateReserve : slots + 3 < 2 ^ w) :
    ((code layout zero terms termCountFits termStorageFits generator default P comparison correct update updateBuffers reserve capacity port draw).lower port).DescriptionFits := by
  have savedFit : Interactive.savedBuffer port
      (WeightedToken.code layout zero terms termCountFits termStorageFits generator default P comparison correct update updateBuffers reserve port draw) < 2 ^ w := by
    have bound := WeightedToken.buffers layout zero terms termCountFits termStorageFits generator default P comparison correct update updateBuffers reserve
      port draw generatorBound drawBound.buffers
    have hw := layout.accumulation.cache.wordFits
    unfold Interactive.savedBuffer
    omega
  exact InteractiveFold.descriptionFits port _ layout.row.representation layout.state.representation
    layout.accumulation.cache.wordFits layout.input.fits
    (WeightedToken.descriptionFits layout zero terms termCountFits termStorageFits generator default P comparison correct update updateBuffers reserve
      port draw generatorBound (by omega) drawFits drawBound (by omega)) savedFit capacity countFits storageFits

end Signatures.Runtime.CaliperBackend.WeightedTokenFold
