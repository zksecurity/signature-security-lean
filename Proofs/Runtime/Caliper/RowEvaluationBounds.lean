import Proofs.Runtime.Caliper.RowEvaluation

/-! Local row budgets include request preparation, the private lookup, saved
frames and the actual accumulator update. -/
namespace Signatures.Runtime.CaliperBackend.RowEvaluation
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat} {Atom : Type} {base : Atom → Type} {key val : Ty Atom} {G F : Type}
    [DecidableEq (key.Value base)] (layout : RowRequest.Layouts w (key.Value base) G F (val.Value base))
    (default : layout.accumulation.cache.value.Value)
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    {combine : F × (val.Value base × val.Value base) → val.Value base}
    (update : Implementation .unit layout.accumulation.combine layout.accumulation.cache.value combine)
    {slots : Nat} (updateBuffers : update.program.code.memBound ≤ slots) (reserve : slots + 2 < 2 ^ w)
    {I : Type} {spec : OracleSpec I} (port : Interactive.Port w spec)

def timeBudget (drawTime updateTime : Nat) : Nat :=
  584 * layout.width + EncodedCacheAccumulate.timeBudget layout.accumulation drawTime updateTime
def codeBudget (drawWords updateWords : Nat) : Nat :=
  1898 * layout.width + 781 + EncodedCacheAccumulate.codeBudget layout.accumulation drawWords updateWords

theorem time_bound {source : OracleComp spec layout.accumulation.cache.value.Value} {draw : Interactive.Code w}
    (drawCorrect : Interactive.Refines port .unit layout.accumulation.cache.lookup.unit.representation
      layout.accumulation.cache.value.representation (fun _ => source) draw)
    {drawTime updateTime updateWords : Nat}
    (drawBound : Interactive.TimeBound port .unit layout.accumulation.cache.lookup.unit.representation draw drawTime)
    (updateBound : update.BoundedBy updateTime updateWords) :
    Interactive.TimeBoundOn (ready layout) port .unit (input layout)
      (code layout default P comparison correct update updateBuffers reserve port draw)
      (timeBudget layout drawTime updateTime) := by
  have prepared := Interactive.Refines.compute port .unit (prepareService layout default)
  have preparedTime := Interactive.TimeBound.compute (port := port) (cost := .unit) (prepareService layout default)
    (584 * layout.width) (fun value => (RowRequest.prepare_bounded layout default).time_le (admitted layout value))
  have readTime := EncodedCacheAccumulate.time_bound layout.accumulation P comparison correct update updateBuffers reserve
    port drawCorrect drawBound updateBound
  have composed := preparedTime.seq prepared readTime
  intro tape value valid before holds finished reached
  exact composed tape ⟨value, valid⟩ before holds finished reached

theorem code_bound (draw : Interactive.Code w) {drawWords updateTime updateWords : Nat}
    (drawBound : (draw.lower port).descriptionWords ≤ drawWords) (updateBound : update.BoundedBy updateTime updateWords) :
    ((code layout default P comparison correct update updateBuffers reserve port draw).lower port).descriptionWords ≤
      codeBudget layout drawWords updateWords := by
  have prepared := (RowRequest.prepare_bounded layout default).code_le
  have read := EncodedCacheAccumulate.code_bound layout.accumulation P comparison correct update updateBuffers reserve port draw drawBound updateBound
  simp only [code, Interactive.Code.lower, WordIO.Code.descriptionWords_seq, WordIO.Code.descriptionWords_compute]
  dsimp only [codeBudget]
  omega

theorem buffers (draw : Interactive.Code w) :
    ((code layout default P comparison correct update updateBuffers reserve port draw).lower port).memBound ≤
      max (max 8 ((draw.lower port).memBound + 1) + 1) (max 4 slots + 1) := by
  have prepared := RowRequest.prepare_buffers layout default
  have read := EncodedCacheAccumulate.buffers layout.accumulation P comparison correct update updateBuffers reserve port draw
  change max (RowRequest.prepare layout default).program.code.memBound _ ≤ _
  omega

theorem names (draw : Interactive.Code w) {drawNames updateNames : Nat}
    (drawBound : WordIO.NamesBound (draw.lower port) drawNames) (updateBound : NamesAccounted update.program.code updateNames) :
    WordIO.NamesAccounted ((code layout default P comparison correct update updateBuffers reserve port draw).lower port)
      (max (max 5 drawNames) updateNames) :=
  (WordIO.NamesAccounted.compute (RowRequest.prepare_names layout default _)).seq
    (EncodedCacheAccumulate.names layout.accumulation P comparison correct update updateBuffers reserve port draw drawBound updateBound)

theorem descriptionFits (draw : Interactive.Code w) (drawFits : (draw.lower port).DescriptionFits) {drawNames : Nat}
    (drawBound : WordIO.NamesBound (draw.lower port) drawNames) (namesFit : drawNames + 2 < 2 ^ w) :
    ((code layout default P comparison correct update updateBuffers reserve port draw).lower port).DescriptionFits :=
  .seq layout.accumulation.cache.wordFits (.compute (RowRequest.prepare layout default).program.description_fits)
    (EncodedCacheAccumulate.descriptionFits layout.accumulation P comparison correct update updateBuffers reserve port draw drawFits drawBound namesFit)

end Signatures.Runtime.CaliperBackend.RowEvaluation
