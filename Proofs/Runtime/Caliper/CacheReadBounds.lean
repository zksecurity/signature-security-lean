import Proofs.Runtime.Caliper.CacheReadCompilation
import Proofs.Runtime.Caliper.CacheReadFinishBounds

/-! Uniform time and stored-code bounds for the complete effectful cache read.
Only the primitive draw supplies a budget. Lookup, branch selection, retaining
the miss frame, projections and insertion all contribute derived overhead. -/

namespace Signatures.Runtime.CaliperBackend.CacheRead

open Caliper BoundedSource OracleComp OracleSpec

variable {w : Nat} {K V I : Type} {spec : OracleSpec I}
    (layout : CacheLayout w K V) (port : Interactive.Port w spec)
    {drawSource : OracleComp spec layout.value.Value} {draw : Interactive.Code w}

theorem draw_time (drawCorrect : Interactive.Refines port .unit layout.lookup.unit.representation layout.value.representation
    (fun _ => drawSource) draw) {drawTime : Nat}
    (drawBound : Interactive.TimeBound port .unit layout.lookup.unit.representation draw drawTime) :
    Interactive.TimeBound port .unit (no layout).representation (drawCode layout port draw)
      (drawTime + 8 * layout.value.representation.encoding.words + 12 * layout.frame.representation.encoding.words) := by
  have retained := drawBound.retain drawCorrect (by decide) (no layout).representation layout.wordFits
    (by change 0 + (no layout).representation.encoding.words < 2 ^ w; simpa using (no layout).representation.fits)
  have viewed := retained.viewInput (no layout).representation (fun frame => (⟨(), trivial⟩, frame)) (fun _ => rfl)
  exact viewed.mono (Interactive.retain_time_unit_le _ 0 _ _ _)

theorem miss_time (drawCorrect : Interactive.Refines port .unit layout.lookup.unit.representation layout.value.representation
    (fun _ => drawSource) draw) {drawTime : Nat}
    (drawBound : Interactive.TimeBound port .unit layout.lookup.unit.representation draw drawTime) :
    Interactive.TimeBound port .unit (no layout).representation (missCode layout port draw)
      (drawTime + 8 * layout.value.representation.encoding.words + 12 * layout.frame.representation.encoding.words + finishTime layout) :=
  (draw_time layout port drawCorrect drawBound).seq (draw_refines drawCorrect)
    (Interactive.TimeBound.compute (port := port) (cost := .unit) (finish layout).program _ (finish_bounded layout).time_le)

def branchTime (drawTime : Nat) : Nat :=
  hitTime layout + drawTime + finishTime layout + 8 * layout.value.representation.encoding.words +
    20 * layout.frame.representation.encoding.words + 2

theorem branch_time (drawCorrect : Interactive.Refines port .unit layout.lookup.unit.representation layout.value.representation
    (fun _ => drawSource) draw) {drawTime : Nat}
    (drawBound : Interactive.TimeBound port .unit layout.lookup.unit.representation draw drawTime) :
    Interactive.TimeBound port .unit (choice layout).representation (branchCode layout port draw) (branchTime layout drawTime) := by
  have hitBound := Interactive.TimeBound.compute (port := port) (cost := .unit) (hit layout).program _ (hit_bounded layout).time_le
  have dispatched := hitBound.dispatch (yes layout).representation (no layout).representation
    (miss_time layout port drawCorrect drawBound) (width_pos layout.wordFits) (by simpa using layout.frame_tagFits)
  have viewed := dispatched.viewInput (choice layout).representation (sumView (yes layout) (no layout)) (fun _ => rfl)
  apply viewed.mono
  rw [Interactive.dispatchTime_unit]
  simp only [yes_words, no_words]
  unfold branchTime
  omega

theorem draw_words (draw : Interactive.Code w) :
    ((drawCode layout port draw).lower port).descriptionWords ≤ (draw.lower port).descriptionWords +
      26 * layout.value.representation.encoding.words + 39 * layout.frame.representation.encoding.words + 41 := by
  simpa only [drawCode, LookupLayout.unit_words, no_words, Nat.mul_zero, Nat.add_zero] using
    Interactive.retain_descriptionWords_le port draw (Interactive.savedBuffer port draw)
      layout.lookup.unit.representation.encoding.words layout.value.representation.encoding.words (no layout).representation.encoding.words

theorem miss_words (draw : Interactive.Code w) :
    ((missCode layout port draw).lower port).descriptionWords ≤ (draw.lower port).descriptionWords +
      26 * layout.value.representation.encoding.words + 39 * layout.frame.representation.encoding.words + finishWords layout + 43 := by
  have drawBound := draw_words layout port draw
  have finishBound := (finish_bounded layout).code_le
  simp only [missCode, Interactive.Code.lower, WordIO.Code.descriptionWords_seq, WordIO.Code.descriptionWords_compute]
  omega

theorem branch_words (draw : Interactive.Code w) :
    ((branchCode layout port draw).lower port).descriptionWords ≤ (draw.lower port).descriptionWords + hitWords layout +
      finishWords layout + 26 * layout.value.representation.encoding.words + 91 * layout.frame.representation.encoding.words + 84 := by
  have missBound := miss_words layout port draw
  have hitBound := (hit_bounded layout).code_le
  simp only [branchCode, Interactive.dispatch_descriptionWords, Interactive.Code.lower,
    WordIO.Code.descriptionWords_compute, yes_words, no_words]
  omega

end Signatures.Runtime.CaliperBackend.CacheRead

namespace Signatures.Runtime.CaliperBackend.EncodedCacheRead

open Caliper BoundedSource SourceExpression OracleComp OracleSpec

variable {w : Nat} {Atom : Type} {base : Atom → Type} {key val : Ty Atom}
    [DecidableEq (key.Value base)] (layout : CacheLayout w (key.Value base) (val.Value base))
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))

def chooseTime : Nat := EncodedLookup.timeBudget (base := base) (key := key) (val := val) layout.lookup +
  136 * layout.lookup.width + 112 * layout.value.representation.encoding.words + 161
def chooseWords : Nat := EncodedLookup.codeBudget (base := base) (key := key) (val := val) layout.lookup +
  442 * layout.lookup.width + 364 * layout.value.representation.encoding.words + 811

theorem choose_bounded : (choose layout P comparison correct).BoundedBy (chooseTime layout) (chooseWords layout) := by
  have bound := (EncodedCache.frame_bounded layout P comparison correct).then
    (GuardedBranch.selector_boundedBy (hw := layout.wordFits) (CacheFinish.test layout) (CacheFinish.test_nameFits layout)
      layout.frame_duplicateFits layout.frame_tagFits (CacheFinish.test_bounded layout))
  apply bound.mono
  all_goals
    simp only [LookupLayout.result_words, CacheLayout.frame_words]
    dsimp only [chooseTime, chooseWords, CacheLayout.lookup]
    omega

def timeBudget (drawTime : Nat) : Nat := EncodedLookup.timeBudget (base := base) (key := key) (val := val) layout.lookup + drawTime +
  404 * layout.lookup.width + 80 * layout.key.representation.encoding.words + 692 * layout.value.representation.encoding.words +
  112 * layout.lookup.table.representation.encoding.words + 420
def codeBudget (drawWords : Nat) : Nat := EncodedLookup.codeBudget (base := base) (key := key) (val := val) layout.lookup + drawWords +
  1339 * layout.lookup.width + 260 * layout.key.representation.encoding.words + 2275 * layout.value.representation.encoding.words +
  364 * layout.lookup.table.representation.encoding.words + 2526

variable {I : Type} {spec : OracleSpec I} (port : Interactive.Port w spec)

theorem time_bound {drawSource : OracleComp spec layout.value.Value} {draw : Interactive.Code w}
    (drawCorrect : Interactive.Refines port .unit layout.lookup.unit.representation layout.value.representation
      (fun _ => drawSource) draw) {drawTime : Nat}
    (drawBound : Interactive.TimeBound port .unit layout.lookup.unit.representation draw drawTime) :
    Interactive.TimeBound port .unit layout.input.representation (code layout P comparison correct port draw) (timeBudget layout drawTime) := by
  have chosenBound := Interactive.TimeBound.compute (port := port) (cost := .unit) (choose layout P comparison correct).program _
    (choose_bounded layout P comparison correct).time_le
  have bound := chosenBound.seq (Interactive.Refines.compute port .unit (choose layout P comparison correct).program)
    (CacheRead.branch_time layout port drawCorrect drawBound)
  apply bound.mono
  dsimp only [chooseTime, timeBudget, CacheRead.branchTime, CacheRead.hitTime, CacheRead.finishTime]
  rw [CacheLayout.frame_words]
  omega

theorem code_bound (draw : Interactive.Code w) {drawWords : Nat} (drawBound : (draw.lower port).descriptionWords ≤ drawWords) :
    ((code layout P comparison correct port draw).lower port).descriptionWords ≤ codeBudget layout drawWords := by
  have chosenBound := (choose_bounded layout P comparison correct).code_le
  have branchBound := CacheRead.branch_words layout port draw
  simp only [code, Interactive.Code.lower, WordIO.Code.descriptionWords_seq, WordIO.Code.descriptionWords_compute]
  dsimp only [chooseWords, codeBudget, CacheRead.hitWords, CacheRead.finishWords] at *
  rw [CacheLayout.frame_words] at branchBound
  omega

end Signatures.Runtime.CaliperBackend.EncodedCacheRead
