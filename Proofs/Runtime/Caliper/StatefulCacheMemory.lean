import Proofs.Runtime.Caliper.StatefulCacheBounds
import Proofs.Runtime.Caliper.CacheReadBuffers
import Proofs.Runtime.Caliper.InteractiveMemory

/-! Stored-word acceptance and complete memory accounting for the same
stateful-cache execution. Initial memory includes all retained caller buffers.
The sampler's names must leave room for the generated saved-frame buffer. -/
namespace Signatures.Runtime.CaliperBackend.StatefulCacheRead
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat} {K V S I : Type} {spec : OracleSpec I}
    (layout : Layouts w K V S) (port : Interactive.Port w spec)

theorem swap_names (slots : Nat) : NamesAccounted (swap layout).code slots := Reorder.names _ _ _ _
theorem shuffle_names (slots : Nat) : NamesAccounted (shuffle layout).code slots :=
  (Reorder.names _ _ _ _).seq (Reorder.names _ _ _ _)
theorem hit_names (slots : Nat) : WordIO.NamesAccounted ((hitCode layout port).lower port) slots :=
  Interactive.retain_names port (body := .compute (CacheRead.hit layout.cache).program.code)
    (WordIO.NamesAccounted.compute (CacheRead.hit_names layout.cache slots)) _ _ _
theorem insert_names (slots : Nat) : WordIO.NamesAccounted ((insertCode layout port).lower port) slots :=
  Interactive.retain_names port (body := .compute (CacheRead.finish layout.cache).program.code)
    (WordIO.NamesAccounted.compute (CacheRead.finish_names layout.cache slots)) _ _ _

theorem branch_names (draw : Interactive.Code w) {slots : Nat}
    (drawNames : WordIO.NamesAccounted (draw.lower port) slots) :
    WordIO.NamesAccounted ((branchCode layout port draw).lower port) slots :=
  Interactive.dispatch_names port (left := hitCode layout port) (right := missCode layout port draw) (hit_names layout port slots)
    ((WordIO.NamesAccounted.compute (swap_names layout slots)).seq
      ((Interactive.retain_names port drawNames _ _ _).seq
        ((WordIO.NamesAccounted.compute (shuffle_names layout slots)).seq (insert_names layout port slots)))) _ _

theorem hit_descriptionFits : ((hitCode layout port).lower port).DescriptionFits :=
  Interactive.retain_descriptionFits port (.compute (CacheRead.hit layout.cache).program.code)
    (Interactive.savedBuffer port (.compute (CacheRead.hit layout.cache).program.code)) _ _ _ layout.cache.wordFits
    (.compute (CacheRead.hit layout.cache).program.description_fits)
    (by have := CacheRead.hit_buffers layout.cache; have := layout.cache.wordFits
        change max 2 (CacheRead.hit layout.cache).program.code.memBound < _; omega)
    (CacheRead.yes layout.cache).representation.fits layout.saved.fits layout.output.fits
theorem insert_descriptionFits : ((insertCode layout port).lower port).DescriptionFits :=
  Interactive.retain_descriptionFits port (.compute (CacheRead.finish layout.cache).program.code)
    (Interactive.savedBuffer port (.compute (CacheRead.finish layout.cache).program.code)) _ _ _ layout.cache.wordFits
    (.compute (CacheRead.finish layout.cache).program.description_fits)
    (by have := CacheRead.finish_buffers layout.cache; have := layout.cache.wordFits
        change max 2 (CacheRead.finish layout.cache).program.code.memBound < _; omega)
    (CacheRead.drawn layout.cache).representation.fits layout.saved.fits layout.output.fits

theorem branch_descriptionFits (draw : Interactive.Code w) (drawFits : (draw.lower port).DescriptionFits)
    (drawName : Interactive.savedBuffer port draw < 2 ^ w) :
    ((branchCode layout port draw).lower port).DescriptionFits :=
  Interactive.dispatch_descriptionFits port _ _ _ _ layout.cache.wordFits (hit_descriptionFits layout port)
    ((WordIO.Code.DescriptionFits.compute (swap layout).description_fits).seq layout.cache.wordFits
      ((Interactive.retain_descriptionFits port draw (Interactive.savedBuffer port draw) _ _ _ layout.cache.wordFits
        drawFits drawName layout.saved.fits (CacheRead.no layout.cache).representation.fits layout.sampled.fits).seq layout.cache.wordFits
        ((WordIO.Code.DescriptionFits.compute (shuffle layout).description_fits).seq layout.cache.wordFits
          (insert_descriptionFits layout port)))) layout.hitInput.fits layout.missInput.fits

section Lookup
variable {Atom : Type} {base : Atom → Type} {key val : Ty Atom} [DecidableEq (key.Value base)]
    (layout : Layouts w (key.Value base) (val.Value base) S)
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))

theorem select_names : WordIO.NamesAccounted ((selectCode port layout P comparison correct).lower port) 5 :=
  (Interactive.retain_names port (body := .compute (EncodedCacheRead.choose layout.cache P comparison correct).program.code)
    (WordIO.NamesAccounted.compute (EncodedCacheRead.choose_names layout.cache P comparison correct)) _ _ _).seq
    (WordIO.NamesAccounted.compute ((SumContext.names _ _ _ _ _).mono (by decide)))

theorem names (draw : Interactive.Code w) {slots : Nat} (drawNames : WordIO.NamesBound (draw.lower port) slots) :
    WordIO.NamesAccounted ((code port layout P comparison correct draw).lower port) (max 5 slots) :=
  ((select_names port layout P comparison correct).mono (Nat.le_max_left _ _)).seq
    (branch_names layout port draw (drawNames.accounted.mono (Nat.le_max_right _ _)))

theorem select_descriptionFits : ((selectCode port layout P comparison correct).lower port).DescriptionFits :=
  (Interactive.retain_descriptionFits port (.compute (EncodedCacheRead.choose layout.cache P comparison correct).program.code)
    (Interactive.savedBuffer port (.compute (EncodedCacheRead.choose layout.cache P comparison correct).program.code)) _ _ _ layout.cache.wordFits
    (.compute (EncodedCacheRead.choose layout.cache P comparison correct).program.description_fits)
    (by have := EncodedCacheRead.choose_buffers layout.cache P comparison correct; have := layout.cache.wordFits
        change max 2 (EncodedCacheRead.choose layout.cache P comparison correct).program.code.memBound < _; omega)
    layout.cache.input.representation.fits layout.saved.fits (choiceFrame layout).fits).seq layout.cache.wordFits
      (.compute (distribute layout).description_fits)

theorem descriptionFits (draw : Interactive.Code w) (drawFits : (draw.lower port).DescriptionFits)
    {slots : Nat} (drawNames : WordIO.NamesBound (draw.lower port) slots) (slotsFit : slots < 2 ^ w) :
    ((code port layout P comparison correct draw).lower port).DescriptionFits :=
  (select_descriptionFits port layout P comparison correct).seq layout.cache.wordFits
    (branch_descriptionFits layout port draw drawFits (by
      have := drawNames.buffers; have := layout.cache.wordFits
      change max 2 (draw.lower port).memBound < _; omega))

theorem resources (source : S → OracleComp spec (layout.cache.value.Value × S)) (draw : Interactive.Code w)
    (drawCorrect : Interactive.Refines port .unit layout.saved layout.freshOutput source draw)
    {drawTime drawWords slots : Nat}
    (drawBound : Interactive.TimeBound port .unit layout.saved draw drawTime)
    (drawStored : (draw.lower port).descriptionWords ≤ drawWords)
    (drawNames : WordIO.NamesBound (draw.lower port) slots)
    (tape : RandomTape w) (value : layout.cache.input.Value × S) (before : State w) (holds : layout.input.Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result w) (reached : some finished ∈ support ((code port layout P comparison correct draw).execute port .unit tape before)) :
    finished.time ≤ timeBudget layout drawTime ∧
      ∃ answer ∈ support (denote layout P comparison correct source value), layout.output.Holds answer finished.state ∧
        ∃ execution : WordIO.Exec .unit tape ((code port layout P comparison correct draw).lower port) before finished.state
            finished.trace finished.time finished.net finished.peak,
          ∀ between, execution.Visits between →
            RegisterBound between (max registers ((code port layout P comparison correct draw).lower port).registerSlots) ∧
            between.SupportBound (max buffers ((code port layout P comparison correct draw).lower port).memBound) ∧ between.WellFormed ∧
            (((code port layout P comparison correct draw).lower port).staticWords registers buffers : Int) +
              between.liveMem (max buffers ((code port layout P comparison correct draw).lower port).memBound) ≤
                5 * codeBudget layout drawWords + 4 * max 5 slots + registers + 3 * buffers + before.liveMem buffers + timeBudget layout drawTime := by
  have refined := refines port layout P comparison correct source draw drawCorrect
  have timed := time_bound port layout P comparison correct drawCorrect drawBound
  have stored := code_bound port layout P comparison correct draw drawStored
  have named := names port layout P comparison correct draw drawNames
  have allNames : WordIO.NamesBound ((code port layout P comparison correct draw).lower port)
      (max 5 slots + codeBudget layout drawWords) :=
    ⟨named.registers.trans (Nat.add_le_add_left stored _), named.buffers.trans (Nat.add_le_add_left stored _)⟩
  obtain ⟨elapsed, answer, supported, result, execution, bounds⟩ :=
    refined.resources timed stored allNames tape value before holds registers buffers initialRegisters initialBuffers finished reached
  refine ⟨elapsed, answer, supported, result, execution, ?_⟩
  intro between visited
  have bounded := bounds between visited
  refine ⟨bounded.1, bounded.2.1, bounded.2.2.1, ?_⟩
  have := bounded.2.2.2
  omega

end Lookup
end Signatures.Runtime.CaliperBackend.StatefulCacheRead
