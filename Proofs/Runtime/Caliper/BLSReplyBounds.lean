import Proofs.Runtime.Caliper.BLSReply
import Proofs.Runtime.Caliper.BLSReplyFinishBounds
import Proofs.Runtime.Caliper.BLSReplyNames
import Proofs.Runtime.Caliper.CacheReadBuffers

/-! Complete BLS reply bounds. The cache budget includes its actual lookup and
insertion; the remaining overhead is linear in the stored frame width. -/

namespace Signatures.Runtime.CaliperBackend.BLSReply
open Caliper BoundedSource OracleComp OracleSpec

variable {w : Nat} {Atom : Type} {base : Atom → Type} {key val : Ty Atom} {C G : Type}
    [DecidableEq (key.Value base)]
    (layout : Layouts w (key.Value base) (val.Value base) C G)
    (default : layout.cache.value.Value) (signing : Bool)
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op) (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    (port : Interactive.Port w unifSpec) (draw : Interactive.Code w)

variable {drawSource : ProbComp layout.cache.value.Value}
    (drawCorrect : Interactive.Refines port .unit layout.cache.lookup.unit.representation layout.cache.value.representation
      (fun _ => drawSource) draw)
    {drawTime drawWords : Nat}
    (drawBound : Interactive.TimeBound port .unit layout.cache.lookup.unit.representation draw drawTime)
    (drawCodeBound : (draw.lower port).descriptionWords ≤ drawWords)

include drawCorrect drawBound in
theorem cache_time : Interactive.TimeBound port .unit (layout.prepared default.val signing).representation
    (cacheCall layout default signing P comparison correct port draw) (EncodedCacheRead.timeBudget layout.cache drawTime + 28 * layout.width) := by
  have retained := (EncodedCacheRead.time_bound layout.cache P comparison correct port drawCorrect drawBound).retain
    (EncodedCacheRead.refines layout.cache P comparison correct port drawSource draw drawCorrect)
    (by decide) (layout.input default.val signing).representation layout.cache.wordFits (layout.prepared default.val signing).representation.fits
  have viewed := retained.viewInput (layout.prepared default.val signing).representation
    (productView layout.cache.input (layout.input default.val signing)) (fun _ => rfl)
  apply viewed.mono
  apply (Interactive.retain_time_unit_le _ _ _ _ _).trans
  simp only [Layouts.cacheInput_words, Layouts.cacheOutput_words, Layouts.input_words, Layouts.plainInput_words]
  dsimp only [Layouts.width]
  rw [Layouts.lookup_width]
  omega

include drawCodeBound in
theorem cache_words : ((cacheCall layout default signing P comparison correct port draw).lower port).descriptionWords ≤
    EncodedCacheRead.codeBudget layout.cache drawWords + 91 * layout.width + 41 := by
  have retained := Interactive.retain_descriptionWords_le port (EncodedCacheRead.code layout.cache P comparison correct port draw)
    (Interactive.savedBuffer port (EncodedCacheRead.code layout.cache P comparison correct port draw))
    layout.cache.input.representation.encoding.words (CacheRead.output layout.cache).representation.encoding.words
    (layout.input default.val signing).representation.encoding.words
  have cached := EncodedCacheRead.code_bound layout.cache P comparison correct port draw drawCodeBound
  change ((cacheCall layout default signing P comparison correct port draw).lower port).descriptionWords ≤ _ at retained
  simp only [Layouts.cacheInput_words, Layouts.cacheOutput_words, Layouts.input_words, Layouts.plainInput_words] at retained
  dsimp only [Layouts.width]
  rw [Layouts.lookup_width] at retained ⊢
  omega

def timeBudget (drawTime responseTime : Nat) : Nat := EncodedCacheRead.timeBudget layout.cache drawTime + responseTime + 2272 * layout.width + 5
def codeBudget (drawWords responseWords : Nat) : Nat := EncodedCacheRead.codeBudget layout.cache drawWords + responseWords + 7384 * layout.width + 2196

variable {respond : val.Value base × C → G} (response : Implementation .unit layout.responseInput layout.point respond)
    {slots : Nat} (responseBuffers : response.program.code.memBound ≤ slots) (reserve : slots + 3 < 2 ^ w)
    {responseTime responseWords : Nat} (responseBound : response.BoundedBy responseTime responseWords)

include drawCorrect drawBound responseBound in
theorem time_bound : Interactive.TimeBound port .unit (layout.input default.val signing).representation
    (code layout default signing P comparison correct port draw response responseBuffers reserve) (timeBudget layout drawTime responseTime) := by
  have first := Interactive.TimeBound.compute (port := port) (cost := .unit) (prepare layout default signing).program _
    (prepare_bounded layout default signing).time_le
  have last := Interactive.TimeBound.compute (port := port) (cost := .unit) (finish layout default signing response responseBuffers reserve).program _
    (finish_bounded layout default signing response responseBuffers reserve responseBound).time_le
  apply (first.seq (Interactive.Refines.compute port .unit (prepare layout default signing).program)
    ((cache_time layout default signing P comparison correct port draw drawCorrect drawBound).seq
      (cache_refines layout default signing P comparison correct port draw drawSource drawCorrect) last)).mono
  dsimp only [timeBudget]
  omega

include drawCodeBound responseBound in
theorem code_bound : ((code layout default signing P comparison correct port draw response responseBuffers reserve).lower port).descriptionWords ≤
    codeBudget layout drawWords responseWords := by
  have first := (prepare_bounded layout default signing).code_le
  have middle := cache_words layout default signing P comparison correct port draw drawCodeBound
  have last := (finish_bounded layout default signing response responseBuffers reserve responseBound).code_le
  simp only [code, Interactive.Code.lower, WordIO.Code.descriptionWords_seq, WordIO.Code.descriptionWords_compute]
  dsimp only [codeBudget]
  omega

theorem names {drawSlots responseSlots : Nat} (drawNames : WordIO.NamesBound (draw.lower port) drawSlots)
    (responseNames : NamesAccounted response.program.code responseSlots) :
    WordIO.NamesAccounted ((code layout default signing P comparison correct port draw response responseBuffers reserve).lower port)
      (max (max 5 drawSlots) responseSlots) := by
  have cached := Interactive.retain_names port
    ((EncodedCacheRead.names layout.cache P comparison correct port draw drawNames).mono (Nat.le_max_left _ responseSlots))
    layout.cache.input.representation.encoding.words (CacheRead.output layout.cache).representation.encoding.words
    (layout.input default.val signing).representation.encoding.words
  exact (WordIO.NamesAccounted.compute (prepare_names layout default signing _)).seq
    (cached.seq (WordIO.NamesAccounted.compute (finish_names layout default signing _ response responseBuffers reserve
      (responseNames.mono (Nat.le_max_right _ _)))))

theorem descriptionFits {drawSlots : Nat} (drawFits : (draw.lower port).DescriptionFits)
    (drawNames : WordIO.NamesBound (draw.lower port) drawSlots) (drawReserve : drawSlots + 1 < 2 ^ w) :
    ((code layout default signing P comparison correct port draw response responseBuffers reserve).lower port).DescriptionFits := by
  have bodyFits := EncodedCacheRead.descriptionFits layout.cache P comparison correct port draw drawFits drawNames (by omega)
  have bodyBuffers := EncodedCacheRead.buffers layout.cache P comparison correct port draw
  have savedFits : Interactive.savedBuffer port (EncodedCacheRead.code layout.cache P comparison correct port draw) < 2 ^ w := by
    have names := drawNames.buffers
    have hw := layout.cache.wordFits
    dsimp only [Interactive.savedBuffer]
    omega
  have cached := Interactive.retain_descriptionFits port _ _ _ _ _ layout.cache.wordFits bodyFits savedFits
    layout.cache.input.representation.fits (layout.input default.val signing).representation.fits
    (layout.post default.val signing).representation.fits
  exact WordIO.Code.DescriptionFits.seq layout.cache.wordFits (.compute (prepare layout default signing).program.description_fits)
    (WordIO.Code.DescriptionFits.seq layout.cache.wordFits cached
      (.compute (finish layout default signing response responseBuffers reserve).program.description_fits))

end Signatures.Runtime.CaliperBackend.BLSReply
