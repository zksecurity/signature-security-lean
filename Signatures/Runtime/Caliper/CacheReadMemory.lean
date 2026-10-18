import Signatures.Runtime.Caliper.CacheReadBounds
import Signatures.Runtime.Caliper.InteractiveNames
import Signatures.Runtime.Caliper.InteractiveAcceptance
import Signatures.Runtime.Caliper.WordFrames

/-! Stored-word acceptance and complete memory bounds for cache reads. Primitive
draw code supplies its actual name/description bounds. The cache derives the
rest, including the saved miss frame, dense metadata and caller-owned capacity. -/

namespace Signatures.Runtime.CaliperBackend.CacheRead

open Caliper BoundedSource

variable {w : Nat} {K V I : Type} {spec : OracleSpec I}
    (layout : CacheLayout w K V) (port : Interactive.Port w spec) (draw : Interactive.Code w)

theorem branch_names {slots : Nat} (drawNames : WordIO.NamesAccounted (draw.lower port) slots) :
    WordIO.NamesAccounted ((branchCode layout port draw).lower port) slots := by
  have savedNames := Interactive.retain_names port drawNames layout.lookup.unit.representation.encoding.words
    layout.value.representation.encoding.words (no layout).representation.encoding.words
  have missNames := savedNames.seq (WordIO.NamesAccounted.compute (finish_names layout slots))
  exact Interactive.dispatch_names port (left := .compute (hit layout).program.code) (right := missCode layout port draw)
    (WordIO.NamesAccounted.compute (hit_names layout slots)) missNames _ _

theorem branch_descriptionFits (drawFits : (draw.lower port).DescriptionFits)
    (nameFits : Interactive.savedBuffer port draw < 2 ^ w) :
    ((branchCode layout port draw).lower port).DescriptionFits := by
  have savedFits := Interactive.retain_descriptionFits port draw (Interactive.savedBuffer port draw)
    layout.lookup.unit.representation.encoding.words layout.value.representation.encoding.words (no layout).representation.encoding.words
    layout.wordFits drawFits nameFits layout.lookup.unit.representation.fits (no layout).representation.fits (drawnFits layout)
  exact Interactive.dispatch_descriptionFits port _ _ _ _ layout.wordFits
    (.compute (hit layout).program.description_fits)
    (WordIO.Code.DescriptionFits.seq layout.wordFits savedFits (.compute (finish layout).program.description_fits))
    (yes layout).representation.fits (no layout).representation.fits

end Signatures.Runtime.CaliperBackend.CacheRead

namespace Signatures.Runtime.CaliperBackend.EncodedCacheRead

open Caliper BoundedSource SourceExpression OracleComp OracleSpec

variable {w : Nat} {Atom : Type} {base : Atom → Type} {key val : Ty Atom}
    [DecidableEq (key.Value base)] (layout : CacheLayout w (key.Value base) (val.Value base))
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))

theorem choose_names : NamesAccounted (choose layout P comparison correct).program.code 5 := by
  have pairedNames : NamesAccounted (EncodedCache.paired layout P comparison correct).program.code 5 :=
    Pairing.names _ _ _ _ _ _ _ _
      (by apply layout.lookup.fits_of_le; simp [LookupLayout.width]; omega)
      (EncodedCache.lookup_names layout P comparison correct) (skip_names 5)
  have testNames : NamesAccounted (CacheFinish.test layout).program.code 5 :=
    (Implementation.first_names _ _ _ _ _).seq (Implementation.first_names _ _ _ _ _)
  exact pairedNames.seq (GuardedBranch.selector_names (hw := layout.wordFits) (CacheFinish.test layout) (CacheFinish.test_nameFits layout)
    layout.frame_duplicateFits layout.frame_tagFits testNames)

variable {I : Type} {spec : OracleSpec I} (port : Interactive.Port w spec) (draw : Interactive.Code w)

theorem names {slots : Nat} (drawNames : WordIO.NamesBound (draw.lower port) slots) :
    WordIO.NamesAccounted ((code layout P comparison correct port draw).lower port) (max 5 slots) :=
  (WordIO.NamesAccounted.compute ((choose_names layout P comparison correct).mono (Nat.le_max_left _ _))).seq
    (CacheRead.branch_names layout port draw (drawNames.accounted.mono (Nat.le_max_right _ _)))

theorem descriptionFits (drawFits : (draw.lower port).DescriptionFits) {slots : Nat}
    (drawNames : WordIO.NamesBound (draw.lower port) slots) (slotsFit : slots < 2 ^ w) :
    ((code layout P comparison correct port draw).lower port).DescriptionFits := by
  have savedFits : Interactive.savedBuffer port draw < 2 ^ w := by
    have bound := drawNames.buffers
    have width := layout.wordFits
    dsimp only [Interactive.savedBuffer]
    omega
  exact WordIO.Code.DescriptionFits.seq layout.wordFits (.compute (choose layout P comparison correct).program.description_fits)
    (CacheRead.branch_descriptionFits layout port draw drawFits savedFits)

theorem staticMemory {drawWords slots : Nat} (drawWordsBound : (draw.lower port).descriptionWords ≤ drawWords)
    (drawNames : WordIO.NamesBound (draw.lower port) slots) (registers buffers : Nat) :
    ((code layout P comparison correct port draw).lower port).staticWords registers buffers ≤
      5 * codeBudget layout drawWords + 4 * max 5 slots + registers + 3 * buffers := by
  have codeBound := code_bound layout P comparison correct port draw drawWordsBound
  have nameBound := names layout P comparison correct port draw drawNames
  rcases nameBound with ⟨registerBound, bufferBound⟩
  unfold WordIO.Code.staticWords
  omega

/-- Every intermediate state belongs to the same actual run with the same
oracle replies. Initial memory includes all caller-owned buffer capacities. -/
theorem memoryBound {drawSource : OracleComp spec layout.value.Value}
    (drawCorrect : Interactive.Refines port .unit layout.lookup.unit.representation layout.value.representation
      (fun _ => drawSource) draw) {drawTime drawWords slots : Nat}
    (drawTimeBound : Interactive.TimeBound port .unit layout.lookup.unit.representation draw drawTime)
    (drawWordsBound : (draw.lower port).descriptionWords ≤ drawWords) (drawNames : WordIO.NamesBound (draw.lower port) slots)
    (tape : RandomTape w) (value : layout.input.Value) (before : State w)
    (holds : layout.input.representation.Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result w) (reached : some finished ∈ support ((code layout P comparison correct port draw).execute port .unit tape before)) :
    finished.time ≤ timeBudget layout drawTime ∧
    ∃ execution : WordIO.Exec .unit tape ((code layout P comparison correct port draw).lower port) before finished.state
        finished.trace finished.time finished.net finished.peak,
      ∀ between, execution.Visits between →
        RegisterBound between (max registers ((code layout P comparison correct port draw).lower port).registerSlots) ∧
        between.SupportBound (max buffers ((code layout P comparison correct port draw).lower port).memBound) ∧ between.WellFormed ∧
        (((code layout P comparison correct port draw).lower port).staticWords registers buffers : Int) +
          between.liveMem (max buffers ((code layout P comparison correct port draw).lower port).memBound) ≤
            5 * codeBudget layout drawWords + 4 * max 5 slots + registers + 3 * buffers + before.liveMem buffers + timeBudget layout drawTime := by
  have refined := refines layout P comparison correct port drawSource draw drawCorrect
  have bounded := time_bound layout P comparison correct port drawCorrect drawTimeBound
  have time := bounded tape value before holds finished reached
  have peak := bounded.bufferPeak refined (by decide) tape value before holds finished reached
  obtain ⟨answer, _, result, equal, _, _, execution⟩ := (refined tape value before holds).right_support reached
  cases Option.some.inj equal
  refine ⟨time, execution, ?_⟩
  intro between visited
  obtain ⟨registerBound, bufferBound, wellFormed, memory⟩ :=
    visited.total_memory_bound registers buffers initialRegisters initialBuffers holds.2.2.1
  refine ⟨registerBound, bufferBound, wellFormed, ?_⟩
  have staticBound := staticMemory layout P comparison correct port draw drawWordsBound drawNames registers buffers
  have initialMemory := liveMem_eq_of_supportBound initialBuffers
    (Nat.le_max_left buffers ((code layout P comparison correct port draw).lower port).memBound)
  omega

end Signatures.Runtime.CaliperBackend.EncodedCacheRead
