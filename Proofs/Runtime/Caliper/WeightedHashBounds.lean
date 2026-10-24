import Proofs.Runtime.Caliper.WeightedHash
import Proofs.Runtime.Caliper.CacheReadBuffers
import Proofs.Runtime.Caliper.CacheReadMemory
import Proofs.Runtime.Caliper.InteractiveInvariantBounds

/-! Full hash costs from the primitive sampler and local group response.
Lookup, retained frames, reply recording and stored code are all included. -/
namespace Signatures.Runtime.CaliperBackend.WeightedHash
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat} {Atom : Type} {base : Atom → Type} {key val : Ty Atom} {M C G : Type}
    [DecidableEq (key.Value base)]
    (layout : Layouts w (key.Value base) M (val.Value base) C G)
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    {I : Type} {spec : OracleSpec I} (port : Interactive.Port w spec) (draw : Interactive.Code w)
    {respond : val.Value base × C → G} (response : Implementation .unit layout.responseInput layout.point respond)
    {slots : Nat} (responseBuffers : response.program.code.memBound ≤ slots) (reserve : slots < 2 ^ w)

def timeBudget (drawTime responseTime : Nat) : Nat :=
  8 * layout.prepared.encoding.words +
    (EncodedCacheRead.timeBudget layout.cache drawTime +
      8 * layout.cache.input.representation.encoding.words + 8 * layout.evaluated.representation.encoding.words +
      12 * layout.input.representation.encoding.words + tailTime layout responseTime)
def codeBudget (drawWords responseWords : Nat) : Nat :=
  (26 * layout.prepared.encoding.words + 15) +
    (EncodedCacheRead.codeBudget layout.cache drawWords +
      26 * layout.cache.input.representation.encoding.words + 26 * layout.evaluated.representation.encoding.words +
      39 * layout.input.representation.encoding.words + 42 + tailWords layout responseWords + 2) + 1

theorem time_bound {source : OracleComp spec layout.cache.value.Value}
    (drawCorrect : Interactive.Refines port .unit layout.cache.lookup.unit.representation
      layout.cache.value.representation (fun _ => source) draw)
    {drawTime responseTime responseWords : Nat}
    (drawBound : Interactive.TimeBound port .unit layout.cache.lookup.unit.representation draw drawTime)
    (responseBound : response.BoundedBy responseTime responseWords) :
    Interactive.TimeBound port .unit layout.input.representation
      (code layout P comparison correct port draw response responseBuffers reserve)
      (timeBudget layout drawTime responseTime) := by
  have cached := EncodedCacheRead.refines layout.cache P comparison correct port source draw drawCorrect
  have kept := cached.retain (by decide) layout.input.representation layout.cache.wordFits layout.prepared.fits layout.post.fits
  have keptTime := ((EncodedCacheRead.time_bound layout.cache P comparison correct port drawCorrect drawBound).retain
    cached (by decide) layout.input.representation layout.cache.wordFits layout.prepared.fits).mono
      (Interactive.retain_time_unit_le _ _ _ _ _)
  have ended := keptTime.seq kept (Interactive.TimeBound.compute (port := port) (cost := .unit)
    (tail layout response responseBuffers reserve) _ (tail_time layout response responseBuffers reserve responseBound))
  have start := Interactive.TimeBound.compute (port := port) (cost := .unit) (prepare layout) _
    (ByteRoute.time _ _ _ (prepareParts layout) layout.cache.wordFits
      (prepareParts_valid layout) (prepareParts_words layout) (prepare_bytes layout))
  exact start.seq (Interactive.Refines.compute port .unit (prepare layout)) ended

theorem code_bound {drawWords responseTime responseWords : Nat}
    (drawBound : (draw.lower port).descriptionWords ≤ drawWords)
    (responseBound : response.BoundedBy responseTime responseWords) :
    ((code layout P comparison correct port draw response responseBuffers reserve).lower port).descriptionWords ≤
      codeBudget layout drawWords responseWords := by
  have cached := EncodedCacheRead.code_bound layout.cache P comparison correct port draw drawBound
  have kept := Interactive.retain_descriptionWords_le port (lookup layout P comparison correct port draw)
    (Interactive.savedBuffer port (lookup layout P comparison correct port draw))
    layout.cache.input.representation.encoding.words layout.evaluated.representation.encoding.words
    layout.input.representation.encoding.words
  have start := ByteRoute.codeWords _ _ _ (prepareParts layout) layout.cache.wordFits
    (prepareParts_valid layout) (prepareParts_words layout) (prepare_bytes layout)
  have ended := tail_words layout response responseBuffers reserve responseBound
  change ((lookup layout P comparison correct port draw).lower port).descriptionWords ≤ _ at cached
  change ((read layout P comparison correct port draw).lower port).descriptionWords ≤ _ at kept
  change descriptionWords (prepare layout).code ≤ _ at start
  simp only [code, Interactive.Code.lower, WordIO.Code.descriptionWords_seq, WordIO.Code.descriptionWords_compute]
  unfold codeBudget
  omega

theorem names {drawSlots responseSlots : Nat}
    (drawBound : WordIO.NamesBound (draw.lower port) drawSlots)
    (responseBound : NamesAccounted response.program.code responseSlots) :
    WordIO.NamesAccounted ((code layout P comparison correct port draw response responseBuffers reserve).lower port)
      (max (max 5 drawSlots) responseSlots) := by
  have cached := Interactive.retain_names port
    ((EncodedCacheRead.names layout.cache P comparison correct port draw drawBound).mono (Nat.le_max_left _ responseSlots))
    layout.cache.input.representation.encoding.words layout.evaluated.representation.encoding.words layout.input.representation.encoding.words
  exact (WordIO.NamesAccounted.compute (ByteRoute.names _ _ _ (prepareParts layout) layout.cache.wordFits
    (prepareParts_valid layout) (prepareParts_words layout) (prepare_bytes layout) _)).seq
    (cached.seq (WordIO.NamesAccounted.compute
      ((tail_names layout response responseBuffers reserve responseBound).mono (Nat.le_max_right _ _))))

theorem descriptionFits {drawSlots : Nat} (drawFits : (draw.lower port).DescriptionFits)
    (drawNames : WordIO.NamesBound (draw.lower port) drawSlots) (drawReserve : drawSlots + 1 < 2 ^ w) :
    ((code layout P comparison correct port draw response responseBuffers reserve).lower port).DescriptionFits := by
  have cachedFits := EncodedCacheRead.descriptionFits layout.cache P comparison correct port draw drawFits drawNames (by omega)
  have cachedBuffers := EncodedCacheRead.buffers layout.cache P comparison correct port draw
  have savedFits : Interactive.savedBuffer port (lookup layout P comparison correct port draw) < 2 ^ w := by
    have names := drawNames.buffers
    have hw := layout.cache.wordFits
    unfold Interactive.savedBuffer lookup
    omega
  have kept := Interactive.retain_descriptionFits port _ _ _ _ _ layout.cache.wordFits cachedFits savedFits
    layout.cache.input.representation.fits layout.input.representation.fits layout.post.fits
  exact .seq layout.cache.wordFits (.compute (prepare layout).description_fits)
    (.seq layout.cache.wordFits kept (.compute (tail layout response responseBuffers reserve).description_fits))

theorem resources {source : OracleComp spec layout.cache.value.Value}
    (drawCorrect : Interactive.Refines port .unit layout.cache.lookup.unit.representation
      layout.cache.value.representation (fun _ => source) draw)
    {drawTime drawWords responseTime responseWords drawNames responseNames : Nat}
    (drawTimeBound : Interactive.TimeBound port .unit layout.cache.lookup.unit.representation draw drawTime)
    (drawWordsBound : (draw.lower port).descriptionWords ≤ drawWords)
    (responseBound : response.BoundedBy responseTime responseWords)
    (drawNamesBound : WordIO.NamesBound (draw.lower port) drawNames)
    (responseNamesBound : NamesAccounted response.program.code responseNames)
    (tape : RandomTape w) (value : layout.input.Value) (before : State w)
    (holds : layout.input.representation.Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result w)
    (reached : some finished ∈ support ((code layout P comparison correct port draw response responseBuffers reserve).execute port .unit tape before)) :
    finished.time ≤ timeBudget layout drawTime responseTime ∧
    ∃ answer ∈ support (denote layout P comparison correct response source value),
      layout.output.representation.Holds answer finished.state ∧
      ∃ execution : WordIO.Exec .unit tape
          ((code layout P comparison correct port draw response responseBuffers reserve).lower port)
          before finished.state finished.trace finished.time finished.net finished.peak,
        ∀ between, execution.Visits between →
          (((code layout P comparison correct port draw response responseBuffers reserve).lower port).staticWords registers buffers : Int) +
            between.liveMem (max buffers ((code layout P comparison correct port draw response responseBuffers reserve).lower port).memBound) ≤
              5 * codeBudget layout drawWords responseWords + 4 * max (max 5 drawNames) responseNames + registers + 3 * buffers +
                before.liveMem buffers + timeBudget layout drawTime responseTime := by
  have stored := code_bound layout P comparison correct port draw response responseBuffers reserve drawWordsBound responseBound
  have named := names layout P comparison correct port draw response responseBuffers reserve drawNamesBound responseNamesBound
  obtain ⟨elapsed, answer, supported, represented, execution, memory⟩ :=
    ((refines layout P comparison correct port draw response responseBuffers reserve drawCorrect).on (fun _ => True)).resources
      ((time_bound layout P comparison correct port draw response responseBuffers reserve drawCorrect drawTimeBound responseBound).on (fun _ => True))
      stored named tape value trivial before holds registers buffers initialRegisters initialBuffers finished reached
  refine ⟨elapsed, answer, supported, represented, execution, ?_⟩
  intro between visited
  have bound := (memory between visited).2.2.2
  omega

end Signatures.Runtime.CaliperBackend.WeightedHash
