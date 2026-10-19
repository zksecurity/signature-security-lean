import Signatures.Runtime.Caliper.StatefulCacheRead
import Signatures.Runtime.Caliper.CacheReadMemory

/-! Derived overhead for the stateful cache. Only the fresh routine supplies a
local budget. Lookup, branch selection, saved frames, permutations and insertion
are charged here, uniformly over every admitted input and oracle reply. -/
namespace Signatures.Runtime.CaliperBackend.StatefulCacheRead
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat} {K V S I : Type} {spec : OracleSpec I}
    (layout : Layouts w K V S) (port : Interactive.Port w spec)

theorem positive : 0 < layout.width := by dsimp only [Layouts.width]; omega

theorem frame_sizes : layout.freshOutput.encoding.words ≤ 2 * layout.width ∧
    layout.hitInput.encoding.words ≤ 2 * layout.width ∧ layout.missInput.encoding.words ≤ 2 * layout.width ∧
    layout.sampled.encoding.words ≤ 3 * layout.width ∧ layout.insertedInput.encoding.words ≤ 3 * layout.width := by
  change (_ + _) ≤ _ ∧ (_ + _) ≤ _ ∧ (_ + _) ≤ _ ∧ ((_ + _) + _) ≤ _ ∧ ((_ + _) + _) ≤ _
  have := layout.sizes
  omega

theorem swap_time (value) : (swap layout).time value ≤ 16 * layout.width :=
  (Pairing.swap_time_unit_le _ _ _ _ value).trans (by have := layout.sizes; omega)
theorem shuffle_time (value) : (shuffle layout).time value ≤ 48 * layout.width := by
  have first := Pairing.swap_time_unit_le layout.freshOutput (CacheRead.no layout.cache).representation
    layout.cache.wordFits layout.sampled.fits value
  have second := Reorder.time_unit_le (w := w) (CacheRead.no layout.cache).representation.encoding.words
    layout.cache.value.representation.encoding.words layout.saved.encoding.words
  change _ + (Assembly.code (Reorder.operands (w := w) (CacheRead.no layout.cache).representation.encoding.words
    layout.cache.value.representation.encoding.words layout.saved.encoding.words)).staticTime .unit ≤ _
  have := layout.sizes
  change _ ≤ 8 * ((_ + _) + _) at first
  omega

theorem hit_time : Interactive.TimeBound port .unit layout.hitInput (hitCode layout port)
    (CacheRead.hitTime layout.cache + 28 * layout.width) := by
  have retained := Interactive.TimeBound.retain
    (Interactive.Refines.compute port .unit (CacheRead.hit layout.cache).program)
    (Interactive.TimeBound.compute (port := port) (cost := .unit) (CacheRead.hit layout.cache).program _
      (CacheRead.hit_bounded layout.cache).time_le)
    (by decide) layout.saved layout.cache.wordFits layout.hitInput.fits
  apply retained.mono
  apply (Interactive.retain_time_unit_le _ _ _ _ _).trans
  have := layout.sizes
  omega

theorem insert_time : Interactive.TimeBound port .unit layout.insertedInput (insertCode layout port)
    (CacheRead.finishTime layout.cache + 36 * layout.width) := by
  have retained := Interactive.TimeBound.retain
    (Interactive.Refines.compute port .unit (CacheRead.finish layout.cache).program)
    (Interactive.TimeBound.compute (port := port) (cost := .unit) (CacheRead.finish layout.cache).program _
      (CacheRead.finish_bounded layout.cache).time_le)
    (by decide) layout.saved layout.cache.wordFits layout.insertedInput.fits
  apply retained.mono
  apply (Interactive.retain_time_unit_le _ _ _ _ _).trans
  change _ + 8 * (_ + _) + _ + _ ≤ _
  have := layout.sizes
  omega

variable {source : S → OracleComp spec (layout.cache.value.Value × S)} {draw : Interactive.Code w}
    (drawCorrect : Interactive.Refines port .unit layout.saved layout.freshOutput source draw)
    {drawTime : Nat} (drawBound : Interactive.TimeBound port .unit layout.saved draw drawTime)

include drawCorrect drawBound in
theorem miss_time : Interactive.TimeBound port .unit layout.missInput (missCode layout port draw)
    (drawTime + CacheRead.finishTime layout.cache + 136 * layout.width) := by
  have retained := (Interactive.TimeBound.retain drawCorrect drawBound (by decide) (CacheRead.no layout.cache).representation
    layout.cache.wordFits (layout.fits_of_le (by have := layout.sizes; omega))).mono
      (Interactive.retain_time_unit_le _ _ _ _ _)
  have bounded := (Interactive.TimeBound.compute (port := port) (cost := .unit) (swap layout) _ (swap_time layout)).seq
    (Interactive.Refines.compute port .unit (swap layout))
    (retained.seq (drawCorrect.retain (by decide) (CacheRead.no layout.cache).representation layout.cache.wordFits
      (layout.fits_of_le (by have := layout.sizes; omega)) layout.sampled.fits)
      ((Interactive.TimeBound.compute (port := port) (cost := .unit) (shuffle layout) _ (shuffle_time layout)).seq
        (Interactive.Refines.compute port .unit (shuffle layout)) (insert_time layout port)))
  apply bounded.mono
  have := layout.sizes
  have := frame_sizes layout
  omega

include drawCorrect drawBound in
theorem branch_time : Interactive.TimeBound port .unit layout.choice (branchCode layout port draw)
    (CacheRead.hitTime layout.cache + CacheRead.finishTime layout.cache + drawTime + 152 * layout.width + 2) := by
  apply ((hit_time layout port).dispatch layout.hitInput layout.missInput (miss_time layout port drawCorrect drawBound)
    (width_pos layout.cache.wordFits) layout.choice.fits).mono
  rw [Interactive.dispatchTime_unit]
  have := frame_sizes layout
  omega

theorem swap_words : descriptionWords (swap layout).code ≤ 52 * layout.width + 14 :=
  (Pairing.swap_descriptionWords_le _ _ _ _ _ _).trans (by have := layout.sizes; omega)
theorem shuffle_words : descriptionWords (shuffle layout).code ≤ 156 * layout.width + 29 := by
  have first := Pairing.swap_descriptionWords_le .unit (by decide) layout.freshOutput
    (CacheRead.no layout.cache).representation layout.cache.wordFits layout.sampled.fits
  have second := Reorder.descriptionWords_le (w := w) (CacheRead.no layout.cache).representation.encoding.words
    layout.cache.value.representation.encoding.words layout.saved.encoding.words
  change descriptionWords (_ ;; _) ≤ _
  rw [descriptionWords_seq]
  change _ + descriptionWords (Assembly.code (Reorder.operands (w := w) (CacheRead.no layout.cache).representation.encoding.words
    layout.cache.value.representation.encoding.words layout.saved.encoding.words)) + 1 ≤ _
  change _ ≤ 26 * ((_ + _) + _) + 14 at first
  have := layout.sizes
  omega

theorem hit_words : ((hitCode layout port).lower port).descriptionWords ≤ CacheRead.hitWords layout.cache + 91 * layout.width + 42 := by
  have retained := Interactive.retain_descriptionWords_le port (.compute (CacheRead.hit layout.cache).program.code)
    (Interactive.savedBuffer port (.compute (CacheRead.hit layout.cache).program.code))
    (CacheRead.yes layout.cache).representation.encoding.words (CacheRead.output layout.cache).representation.encoding.words
    layout.saved.encoding.words
  have body := (CacheRead.hit_bounded layout.cache).code_le
  change _ ≤ descriptionWords (CacheRead.hit layout.cache).program.code + 1 + _ + _ + _ + _ at retained
  have := layout.sizes
  exact retained.trans (by omega)

theorem insert_words : ((insertCode layout port).lower port).descriptionWords ≤ CacheRead.finishWords layout.cache + 117 * layout.width + 42 := by
  have retained := Interactive.retain_descriptionWords_le port (.compute (CacheRead.finish layout.cache).program.code)
    (Interactive.savedBuffer port (.compute (CacheRead.finish layout.cache).program.code))
    (CacheRead.drawn layout.cache).representation.encoding.words (CacheRead.output layout.cache).representation.encoding.words
    layout.saved.encoding.words
  have body := (CacheRead.finish_bounded layout.cache).code_le
  change _ ≤ descriptionWords (CacheRead.finish layout.cache).program.code + 1 + 26 * (_ + _) + _ + _ + _ at retained
  have := layout.sizes
  exact retained.trans (by omega)

theorem miss_words (draw : Interactive.Code w) {drawWords : Nat} (drawBound : (draw.lower port).descriptionWords ≤ drawWords) :
    ((missCode layout port draw).lower port).descriptionWords ≤ drawWords + CacheRead.finishWords layout.cache + 442 * layout.width + 131 := by
  have retained := Interactive.retain_descriptionWords_le port draw (Interactive.savedBuffer port draw)
    layout.saved.encoding.words layout.freshOutput.encoding.words (CacheRead.no layout.cache).representation.encoding.words
  have first := swap_words layout
  have shuffled := shuffle_words layout
  have inserted := insert_words layout port
  have := layout.sizes
  have := frame_sizes layout
  simp only [missCode, Interactive.Code.lower, WordIO.Code.descriptionWords_seq, WordIO.Code.descriptionWords_compute]
  omega

theorem branch_words (draw : Interactive.Code w) {drawWords : Nat} (drawBound : (draw.lower port).descriptionWords ≤ drawWords) :
    ((branchCode layout port draw).lower port).descriptionWords ≤
      CacheRead.hitWords layout.cache + CacheRead.finishWords layout.cache + drawWords + 637 * layout.width + 213 := by
  have hit := hit_words layout port
  have miss := miss_words layout port draw drawBound
  have := frame_sizes layout
  rw [branchCode, Interactive.dispatch_descriptionWords]
  omega

section Lookup
variable {Atom : Type} {base : Atom → Type} {key val : Ty Atom} [DecidableEq (key.Value base)]
    (layout : Layouts w (key.Value base) (val.Value base) S)
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))

omit [DecidableEq (key.Value base)] in
theorem choice_sizes : (CacheRead.choice layout.cache).representation.encoding.words ≤ 2 * layout.width ∧
    (choiceFrame layout).encoding.words ≤ 3 * layout.width := by
  have := layout.sizes
  have := positive layout
  change 1 + max _ _ ≤ _ ∧ (1 + max _ _) + _ ≤ _
  omega

theorem select_time : Interactive.TimeBound port .unit layout.input (selectCode port layout P comparison correct)
    (EncodedCacheRead.chooseTime layout.cache + 108 * layout.width + 2) := by
  have retained := (Interactive.TimeBound.retain
    (Interactive.Refines.compute port .unit (EncodedCacheRead.choose layout.cache P comparison correct).program)
    (Interactive.TimeBound.compute (port := port) (cost := .unit) (EncodedCacheRead.choose layout.cache P comparison correct).program _
      (EncodedCacheRead.choose_bounded layout.cache P comparison correct).time_le)
    (by decide) layout.saved layout.cache.wordFits layout.input.fits).mono
      (Interactive.retain_time_unit_le _ _ _ _ _)
  have distributed := Interactive.TimeBound.compute (port := port) (cost := .unit) (distribute layout)
    (24 * (choiceFrame layout).encoding.words + 2)
    (fun value => SumContext.time _ _ _ _ _ (sumView (CacheRead.yes layout.cache) (CacheRead.no layout.cache) value.1, value.2))
  have bounded := retained.seq
    ((Interactive.Refines.compute port .unit (EncodedCacheRead.choose layout.cache P comparison correct).program).retain
      (by decide) layout.saved layout.cache.wordFits layout.input.fits (choiceFrame layout).fits) distributed
  apply bounded.mono
  have sizes := layout.sizes
  have := choice_sizes layout
  change layout.cache.input.representation.encoding.words ≤ _ ∧ _ at sizes
  omega

def timeBudget (drawTime : Nat) : Nat :=
  EncodedCacheRead.chooseTime (base := base) (key := key) (val := val) layout.cache + CacheRead.hitTime layout.cache +
    CacheRead.finishTime layout.cache + drawTime + 300 * layout.width + 10
def codeBudget (drawWords : Nat) : Nat :=
  EncodedCacheRead.chooseWords (base := base) (key := key) (val := val) layout.cache + CacheRead.hitWords layout.cache +
    CacheRead.finishWords layout.cache + drawWords + 1400 * layout.width + 400

theorem time_bound {source : S → OracleComp spec (layout.cache.value.Value × S)} {draw : Interactive.Code w}
    (drawCorrect : Interactive.Refines port .unit layout.saved layout.freshOutput source draw)
    {drawTime : Nat} (drawBound : Interactive.TimeBound port .unit layout.saved draw drawTime) :
    Interactive.TimeBound port .unit layout.input (code port layout P comparison correct draw) (timeBudget layout drawTime) := by
  apply ((select_time port layout P comparison correct).seq (select_refines port layout P comparison correct)
    (branch_time layout port drawCorrect drawBound)).mono
  dsimp only [timeBudget]
  omega

theorem select_words : ((selectCode port layout P comparison correct).lower port).descriptionWords ≤
    EncodedCacheRead.chooseWords layout.cache + 585 * layout.width + 139 := by
  have retained := Interactive.retain_descriptionWords_le port
    (.compute (EncodedCacheRead.choose layout.cache P comparison correct).program.code)
    (Interactive.savedBuffer port (.compute (EncodedCacheRead.choose layout.cache P comparison correct).program.code))
    layout.cache.input.representation.encoding.words (CacheRead.choice layout.cache).representation.encoding.words layout.saved.encoding.words
  have chosen := (EncodedCacheRead.choose_bounded layout.cache P comparison correct).code_le
  have distributed := SumContext.words (CacheRead.yes layout.cache).representation (CacheRead.no layout.cache).representation
    layout.saved layout.cache.wordFits (choiceFrame layout).fits
  change descriptionWords (distribute layout).code ≤ 156 * (choiceFrame layout).encoding.words + 95 at distributed
  change _ ≤ descriptionWords (EncodedCacheRead.choose layout.cache P comparison correct).program.code + 1 + _ + _ + _ + _ at retained
  have sizes := layout.sizes
  have choice := choice_sizes layout
  change layout.cache.input.representation.encoding.words ≤ _ ∧ _ at sizes
  simp only [selectCode, Interactive.Code.lower, WordIO.Code.descriptionWords_seq, WordIO.Code.descriptionWords_compute]
  omega

theorem code_bound (draw : Interactive.Code w) {drawWords : Nat} (drawBound : (draw.lower port).descriptionWords ≤ drawWords) :
    ((code port layout P comparison correct draw).lower port).descriptionWords ≤ codeBudget layout drawWords := by
  have first := select_words port layout P comparison correct
  have second := branch_words layout port draw drawBound
  simp only [code, Interactive.Code.lower, WordIO.Code.descriptionWords_seq]
  dsimp only [codeBudget]
  omega
end Lookup
end Signatures.Runtime.CaliperBackend.StatefulCacheRead
