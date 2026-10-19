import Signatures.Runtime.Caliper.StatefulCacheLayout
import Signatures.Runtime.Caliper.Reorder

/-! Executed cache access with a stateful fresh-entry routine. Hits bypass that
routine completely. Misses save the cache frame outside the routine's footprint,
then insert its returned entry and return its updated represented state. -/
namespace Signatures.Runtime.CaliperBackend.StatefulCacheRead
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat} {K V S I : Type} {spec : OracleSpec I}
    (layout : Layouts w K V S) (port : Interactive.Port w spec)

def hitValue (value : (CacheRead.yes layout.cache).Value × S) : (CacheRead.output layout.cache).Value × S :=
  (⟨(value.1.val.1.2, value.1.val.2.2.2.1), (CacheRead.hit layout.cache).preserves value.1.val value.1.property⟩, value.2)
def hitCode : Interactive.Code w :=
  Interactive.retain (.compute (CacheRead.hit layout.cache).program.code)
    (Interactive.savedBuffer port (.compute (CacheRead.hit layout.cache).program.code))
    (CacheRead.yes layout.cache).representation.encoding.words
    (CacheRead.output layout.cache).representation.encoding.words layout.saved.encoding.words

theorem hit_refines : Interactive.Refines port .unit layout.hitInput layout.output
    (fun value => pure (hitValue layout value)) (hitCode layout port) := by
  have retained := (Interactive.Refines.compute port .unit (CacheRead.hit layout.cache).program).retain
    (by decide) layout.saved layout.cache.wordFits layout.hitInput.fits layout.output.fits
  convert retained using 1 <;> rfl

def swap : Realizer .unit layout.missInput
    (layout.saved.prod (CacheRead.no layout.cache).representation (layout.fits_of_le (by have := layout.sizes; omega))) Prod.swap :=
  Pairing.swap .unit (by decide) (CacheRead.no layout.cache).representation layout.saved layout.cache.wordFits layout.missInput.fits

/-- `(entry, new state, saved frame)` is physically permuted to
`(entry, saved frame, new state)` before insertion. -/
def shuffle : Realizer .unit layout.sampled layout.insertedInput
    (fun value => (CacheRead.drawnValue layout.cache value.2 value.1.1, value.1.2)) :=
  ((Pairing.swap .unit (by decide) layout.freshOutput (CacheRead.no layout.cache).representation
      layout.cache.wordFits layout.sampled.fits).then
    (Reorder.realizer .unit (by decide) (CacheRead.no layout.cache).representation layout.cache.value.representation
      layout.saved layout.cache.wordFits (layout.fits_of_le (by have := layout.sizes; omega)))).viewOutput
        layout.insertedInput (fun value => (CacheRead.drawnValue layout.cache value.2 value.1.1, value.1.2)) (by
          intro value
          change (_ ++ _) ++ _ = _ ++ (_ ++ _)
          exact List.append_assoc _ _ _)

def insertCode : Interactive.Code w :=
  Interactive.retain (.compute (CacheRead.finish layout.cache).program.code)
    (Interactive.savedBuffer port (.compute (CacheRead.finish layout.cache).program.code))
    (CacheRead.drawn layout.cache).representation.encoding.words
    (CacheRead.output layout.cache).representation.encoding.words layout.saved.encoding.words

theorem insert_refines : Interactive.Refines port .unit layout.insertedInput layout.output
    (fun value => pure (CacheRead.completed layout.cache value.1, value.2)) (insertCode layout port) := by
  have retained := (Interactive.Refines.compute port .unit (CacheRead.finish layout.cache).program).retain
    (by decide) layout.saved layout.cache.wordFits layout.insertedInput.fits layout.output.fits
  convert retained using 1 <;> rfl

def missCode (draw : Interactive.Code w) : Interactive.Code w :=
  .seq (.compute (swap layout).code)
    (.seq (Interactive.retain draw (Interactive.savedBuffer port draw) layout.saved.encoding.words
      layout.freshOutput.encoding.words (CacheRead.no layout.cache).representation.encoding.words)
      (.seq (.compute (shuffle layout).code) (insertCode layout port)))

def missDenote (source : S → OracleComp spec (layout.cache.value.Value × S))
    (value : (CacheRead.no layout.cache).Value × S) : OracleComp spec ((CacheRead.output layout.cache).Value × S) :=
  (fun fresh => (CacheRead.completed layout.cache (CacheRead.drawnValue layout.cache value.1 fresh.1), fresh.2)) <$> source value.2

variable {source : S → OracleComp spec (layout.cache.value.Value × S)} {draw : Interactive.Code w}
    (drawCorrect : Interactive.Refines port .unit layout.saved layout.freshOutput source draw)

include drawCorrect in
theorem miss_refines : Interactive.Refines port .unit layout.missInput layout.output
    (missDenote layout source) (missCode layout port draw) := by
  have retained := drawCorrect.retain (by decide) (CacheRead.no layout.cache).representation layout.cache.wordFits
    (layout.fits_of_le (by have := layout.sizes; omega)) layout.sampled.fits
  have compiled := (Interactive.Refines.compute port .unit (swap layout)).seq
    (retained.seq ((Interactive.Refines.compute port .unit (shuffle layout)).seq (insert_refines layout port)))
  convert compiled using 1
  · funext value
    simp only [pure_bind, map_pure, bind_pure_comp, Functor.map_map, missDenote]
    rfl
  · rfl

def branchCode (draw : Interactive.Code w) : Interactive.Code w :=
  Interactive.dispatch (hitCode layout port) (missCode layout port draw)
    layout.hitInput.encoding.words layout.missInput.encoding.words

def branchDenote (source : S → OracleComp spec (layout.cache.value.Value × S)) :
    ((CacheRead.yes layout.cache).Value × S) ⊕ ((CacheRead.no layout.cache).Value × S) →
      OracleComp spec ((CacheRead.output layout.cache).Value × S) :=
  Sum.elim (fun value => pure (hitValue layout value)) (missDenote layout source)

include drawCorrect in
theorem branch_refines : Interactive.Refines port .unit layout.choice layout.output
    (branchDenote layout source) (branchCode layout port draw) :=
  Interactive.Refines.dispatch layout.hitInput layout.missInput layout.output (hit_refines layout port)
    (miss_refines layout port drawCorrect) (width_pos layout.cache.wordFits) layout.choice.fits

section Lookup
variable {Atom : Type} {base : Atom → Type} {key val : Ty Atom} [DecidableEq (key.Value base)]
    (layout : Layouts w (key.Value base) (val.Value base) S)
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))

def choiceFrame : Representation w ((CacheRead.choice layout.cache).Value × S) :=
  (CacheRead.choice layout.cache).representation.prod layout.saved (layout.fits_of_le (by
    change (1 + max (CacheRead.yes layout.cache).representation.encoding.words
      (CacheRead.no layout.cache).representation.encoding.words) + _ ≤ _
    have positive : 0 < layout.width := by dsimp only [Layouts.width]; omega
    have := layout.sizes; omega))

def distribute : Realizer .unit (choiceFrame layout) layout.choice
    (fun value => SumContext.view (sumView (CacheRead.yes layout.cache) (CacheRead.no layout.cache) value.1, value.2)) :=
  (SumContext.distribute (CacheRead.yes layout.cache).representation (CacheRead.no layout.cache).representation
    layout.saved layout.cache.wordFits (choiceFrame layout).fits).viewInput (choiceFrame layout)
      (fun value => (sumView (CacheRead.yes layout.cache) (CacheRead.no layout.cache) value.1, value.2)) (fun _ => rfl)

def selectCode : Interactive.Code w :=
  .seq (Interactive.retain (.compute (EncodedCacheRead.choose layout.cache P comparison correct).program.code)
    (Interactive.savedBuffer port (.compute (EncodedCacheRead.choose layout.cache P comparison correct).program.code))
    layout.cache.input.representation.encoding.words (CacheRead.choice layout.cache).representation.encoding.words
    layout.saved.encoding.words) (.compute (distribute layout).code)

def selected (value : layout.cache.input.Value × S) :
    ((CacheRead.yes layout.cache).Value × S) ⊕ ((CacheRead.no layout.cache).Value × S) :=
  SumContext.view (sumView (CacheRead.yes layout.cache) (CacheRead.no layout.cache)
    (EncodedCacheRead.chosen layout.cache P comparison correct value.1), value.2)

theorem select_refines : Interactive.Refines port .unit layout.input layout.choice
    (fun value => pure (selected layout P comparison correct value)) (selectCode port layout P comparison correct) := by
  have retained := (Interactive.Refines.compute port .unit (EncodedCacheRead.choose layout.cache P comparison correct).program).retain
    (by decide) layout.saved layout.cache.wordFits layout.input.fits (choiceFrame layout).fits
  convert retained.seq (Interactive.Refines.compute port .unit (distribute layout)) using 1 <;> rfl

def code (draw : Interactive.Code w) : Interactive.Code w :=
  .seq (selectCode port layout P comparison correct) (branchCode layout port draw)

def denote (source : S → OracleComp spec (layout.cache.value.Value × S)) (value : layout.cache.input.Value × S) :
    OracleComp spec ((CacheRead.output layout.cache).Value × S) :=
  branchDenote layout source (selected layout P comparison correct value)

theorem refines (source : S → OracleComp spec (layout.cache.value.Value × S)) (draw : Interactive.Code w)
    (drawCorrect : Interactive.Refines port .unit layout.saved layout.freshOutput source draw) :
    Interactive.Refines port .unit layout.input layout.output (denote layout P comparison correct source)
      (code port layout P comparison correct draw) := by
  convert (select_refines port layout P comparison correct).seq (branch_refines layout port drawCorrect) using 1
  · funext value
    simp only [pure_bind]
    rfl
  · rfl

theorem denote_value (source : S → OracleComp spec (layout.cache.value.Value × S)) (value : layout.cache.input.Value × S) :
    (fun result => (result.1.val, result.2)) <$> denote layout P comparison correct source value =
      if ((lookupExpr comparison).denote P value.1.val).1 = true then
        pure ((((lookupExpr comparison).denote P value.1.val).2, value.1.val.2.2.1), value.2)
      else (fun fresh => ((fresh.1.val, (value.1.val.1, fresh.1.val) :: value.1.val.2.2.1), fresh.2)) <$> source value.2 := by
  by_cases found : ((lookupExpr comparison).denote P value.1.val).1 = true <;>
    simp [denote, selected, EncodedCacheRead.chosen, GuardedBranch.select, sumView, SumContext.view,
      branchDenote, hitValue, missDenote, CacheRead.completed, CacheRead.drawnValue, found, Functor.map_map]

end Lookup
end Signatures.Runtime.CaliperBackend.StatefulCacheRead
