import Signatures.Runtime.Caliper.CallerStep
import Signatures.Runtime.Caliper.InteractiveAcceptance

/-! The generated caller step adds linear copying/control overhead to the
actual handler and caller-continuation budgets. Stored code includes both local
implementations and all save/restore and permutation instructions. -/

namespace Signatures.Runtime.CaliperBackend.CallerStep
open Caliper OracleComp OracleSpec

variable {w : Nat} {C Q R B S : Type} (layout : Layouts w C Q R B S)

def width : Nat := 1 + layout.state.encoding.words + layout.request.encoding.words +
  layout.reply.encoding.words + layout.result.encoding.words + layout.store.encoding.words

theorem prepare_time (value : (Q × C) × S) : (prepare layout).time value ≤ 16 * width layout := by
  have first := Pairing.swap_time_unit_le (pending layout) layout.store layout.width (frame layout).fits value
  have second := Reorder.time_unit_le (w := w) layout.store.encoding.words layout.request.encoding.words layout.state.encoding.words
  change _ + _ ≤ _
  change _ ≤ 8 * (layout.request.encoding.words + layout.state.encoding.words + layout.store.encoding.words) at first
  dsimp only [width]
  exact (Nat.add_le_add first second).trans (by omega)

theorem prepare_words : descriptionWords (prepare layout).code ≤ 52 * width layout + 29 := by
  have first := Pairing.swap_descriptionWords_le .unit (by decide) (pending layout) layout.store layout.width (frame layout).fits
  have second := Reorder.descriptionWords_le (w := w) layout.store.encoding.words layout.request.encoding.words layout.state.encoding.words
  change descriptionWords (_ ;; _) ≤ _
  rw [descriptionWords_seq]
  dsimp only [Reorder.realizer, Assembly.realizer]
  change _ ≤ 26 * (layout.request.encoding.words + layout.state.encoding.words + layout.store.encoding.words) + 14 at first
  dsimp only [width]
  omega

theorem resume_time (value : (R × S) × C) : (resumeArgs layout).time value ≤ 8 * width layout := by
  exact (Pairing.swap_time_unit_le (reply layout) layout.state layout.width (savedReply layout).fits value).trans (by
    change 8 * (layout.reply.encoding.words + layout.store.encoding.words + layout.state.encoding.words) ≤ _
    dsimp only [width]
    omega)

theorem resume_words : descriptionWords (resumeArgs layout).code ≤ 26 * width layout + 14 := by
  exact (Pairing.swap_descriptionWords_le .unit (by decide) (reply layout) layout.state layout.width (savedReply layout).fits).trans (by
    change 26 * (layout.reply.encoding.words + layout.store.encoding.words + layout.state.encoding.words) + 14 ≤ _
    dsimp only [width]
    omega)

variable {I : Type} {spec : OracleSpec I} (port : Interactive.Port w spec)
    (advance : C × R → B ⊕ (Q × C))
    (continuation : Realizer .unit (resume layout) (next layout) advance)
    (localNameFits : continuation.savedBuffer < 2 ^ w)

theorem continue_time {budget : Nat} (bounded : ∀ value, continuation.time value ≤ budget)
    (value : (C × R) × S) : (continueCode layout advance continuation localNameFits).time value ≤
      budget + 28 * width layout := by
  have copied := continuation.retain_time_unit_le layout.store layout.width localNameFits
    (savedResume layout).fits (output layout).fits value
  have elapsed := bounded value.1
  change _ ≤ continuation.time value.1 + 8 * (layout.state.encoding.words + layout.reply.encoding.words) +
    8 * (1 + max layout.result.encoding.words (layout.request.encoding.words + layout.state.encoding.words)) +
    12 * layout.store.encoding.words at copied
  dsimp only [width]
  exact copied.trans (by omega)

theorem continue_words : descriptionWords (continueCode layout advance continuation localNameFits).code ≤
    descriptionWords continuation.code + 91 * width layout + 39 := by
  have copied := continuation.retain_descriptionWords_le (by decide) layout.store layout.width localNameFits
    (savedResume layout).fits (output layout).fits
  change _ ≤ descriptionWords continuation.code + 26 * (layout.state.encoding.words + layout.reply.encoding.words) +
    26 * (1 + max layout.result.encoding.words (layout.request.encoding.words + layout.state.encoding.words)) +
    39 * layout.store.encoding.words + 39 at copied
  dsimp only [width]
  exact copied.trans (by omega)

theorem time {ready : Q × S → Prop} {handlerSource : Q × S → OracleComp spec (R × S)}
    {handler : Interactive.Code w} {handlerTime localTime : Nat}
    (handlerRefines : Interactive.RefinesOn ready port .unit (request layout) (reply layout) handlerSource handler)
    (handlerBound : Interactive.TimeBoundOn ready port .unit (request layout) handler handlerTime)
    (localBound : ∀ value, continuation.time value ≤ localTime) :
    Interactive.TimeBoundOn (fun value => ready (value.1.1, value.2)) port .unit (frame layout)
      (code layout port advance continuation localNameFits handler) (handlerTime + localTime + 80 * width layout) := by
  have retainedRefines := handlerRefines.retain (by decide) layout.state layout.width
    (savedRequest layout).fits (savedReply layout).fits
  have retainedBound := (Interactive.TimeBoundOn.retain handlerRefines handlerBound (by decide)
    layout.state layout.width (savedRequest layout).fits).mono
      ((Interactive.retain_time_unit_le (w := w) _ _ _ _ handlerTime).trans (show
        handlerTime + 8 * (request layout).encoding.words + 8 * (reply layout).encoding.words +
          12 * layout.state.encoding.words ≤ handlerTime + 28 * width layout from by
        change handlerTime + 8 * (layout.request.encoding.words + layout.store.encoding.words) +
          8 * (layout.reply.encoding.words + layout.store.encoding.words) + 12 * layout.state.encoding.words ≤ _
        dsimp only [width]
        omega))
  have resumeBound := Interactive.TimeBound.compute (port := port) (cost := .unit)
    ((resumeArgs layout).then (continueCode layout advance continuation localNameFits))
    (localTime + 36 * width layout) (by
      intro value
      have first := resume_time layout value
      have second := continue_time layout advance continuation localNameFits localBound
        ((value.2, value.1.1), value.1.2)
      exact (Nat.add_le_add first second).trans (by omega))
  have invoked := Interactive.TimeBoundOn.seq retainedRefines retainedBound
    (resumeBound.on (fun _ => True)) (by intros; trivial)
  have prepared := (Interactive.Refines.compute port .unit (prepare layout)).on
    (fun value => ready (value.1.1, value.2))
  have combined := Interactive.TimeBoundOn.seq prepared
    ((Interactive.TimeBound.compute (port := port) (cost := .unit) (prepare layout) _ (prepare_time layout)).on _)
    invoked (by
      intro value valid answer reached
      simp only [support_pure, Set.mem_singleton_iff] at reached
      subst answer
      exact valid)
  exact combined.mono (by omega)

theorem words (handler : Interactive.Code w) :
    ((code layout port advance continuation localNameFits handler).lower port).descriptionWords ≤
      (handler.lower port).descriptionWords + descriptionWords continuation.code + 260 * width layout + 128 := by
  have prepared := prepare_words layout
  have resumed := resume_words layout
  have continued := continue_words layout advance continuation localNameFits
  have retained := Interactive.retain_descriptionWords_le port handler (Interactive.savedBuffer port handler)
    (request layout).encoding.words (reply layout).encoding.words layout.state.encoding.words
  change _ ≤ (handler.lower port).descriptionWords +
    26 * (layout.request.encoding.words + layout.store.encoding.words) +
    26 * (layout.reply.encoding.words + layout.store.encoding.words) + 39 * layout.state.encoding.words + 41 at retained
  simp only [code, Interactive.Code.lower, WordIO.Code.descriptionWords_seq, WordIO.Code.descriptionWords_compute,
    Realizer.then, descriptionWords_seq]
  dsimp only [width] at *
  omega

theorem descriptionFits {handler : Interactive.Code w} (accepted : (handler.lower port).DescriptionFits)
    (handlerNameFits : Interactive.savedBuffer port handler < 2 ^ w) :
    ((code layout port advance continuation localNameFits handler).lower port).DescriptionFits := by
  exact WordIO.Code.DescriptionFits.seq layout.width
    (WordIO.Code.DescriptionFits.compute (prepare layout).description_fits)
    (WordIO.Code.DescriptionFits.seq layout.width
      (Interactive.retain_descriptionFits port handler _ _ _ _ layout.width accepted handlerNameFits
        (request layout).fits layout.state.fits (savedReply layout).fits)
      (WordIO.Code.DescriptionFits.compute
        ((resumeArgs layout).then (continueCode layout advance continuation localNameFits)).description_fits))

theorem names {handler : Interactive.Code w} {slots : Nat}
    (handlerNames : WordIO.NamesAccounted (handler.lower port) slots)
    (localNames : NamesAccounted continuation.code slots) :
    WordIO.NamesAccounted ((code layout port advance continuation localNameFits handler).lower port) slots := by
  have prepared : NamesAccounted (prepare layout).code slots :=
    (Reorder.names (pending layout).encoding.words layout.store.encoding.words 0 slots).seq
      (Reorder.names layout.store.encoding.words layout.request.encoding.words layout.state.encoding.words slots)
  have resumed : NamesAccounted (resumeArgs layout).code slots :=
    Reorder.names (reply layout).encoding.words layout.state.encoding.words 0 slots
  have continued : NamesAccounted (continueCode layout advance continuation localNameFits).code slots :=
    Retain.names localNames _ _ _
  exact (WordIO.NamesAccounted.compute prepared).seq
    ((Interactive.retain_names port handlerNames _ _ _).seq
      (WordIO.NamesAccounted.compute (resumed.seq continued)))

end Signatures.Runtime.CaliperBackend.CallerStep
