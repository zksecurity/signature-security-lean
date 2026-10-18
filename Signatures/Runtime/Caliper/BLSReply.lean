import Signatures.Runtime.Caliper.BLSReplyFinish
import Signatures.Runtime.LazyAGMExecution

/-! Complete private BLS reply execution: prepare, retain the caller frame
across the actual lazy cache, calculate the response, record it and return the
updated store. Source equality preserves the reply, configuration, cache and logs. -/

namespace Signatures.Runtime.CaliperBackend.BLSReply

open Caliper BoundedSource OracleComp OracleSpec

variable {w : Nat} {Atom : Type} {base : Atom → Type} {key val : Ty Atom} {C G : Type}
    [DecidableEq (key.Value base)]
    (layout : Layouts w (key.Value base) (val.Value base) C G)
    (default : layout.cache.value.Value) (signing : Bool)
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op) (comparison : Expr Op [key, key] .bool)
    (comparisonCorrect : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    (port : Interactive.Port w unifSpec) (draw : Interactive.Code w)

def cacheCall : Interactive.Code w :=
  Interactive.retain (EncodedCacheRead.code layout.cache P comparison comparisonCorrect port draw)
    (Interactive.savedBuffer port (EncodedCacheRead.code layout.cache P comparison comparisonCorrect port draw))
    layout.cache.input.representation.encoding.words (CacheRead.output layout.cache).representation.encoding.words
    (layout.input default.val signing).representation.encoding.words

def cachedValue (value : (layout.prepared default.val signing).Value) (answer : (CacheRead.output layout.cache).Value) :
    (layout.post default.val signing).Value := ⟨(answer.val, value.val.2), answer.property, value.property.2⟩

def cachedDenote (drawSource : ProbComp layout.cache.value.Value) (value : (layout.prepared default.val signing).Value) :
    ProbComp (layout.post default.val signing).Value :=
  cachedValue layout default signing value <$> EncodedCacheRead.denote layout.cache P comparison comparisonCorrect drawSource
    ⟨value.val.1, value.property.1⟩

theorem cache_refines (drawSource : ProbComp layout.cache.value.Value)
    (drawCorrect : Interactive.Refines port .unit layout.cache.lookup.unit.representation layout.cache.value.representation
      (fun _ => drawSource) draw) :
    Interactive.Refines port .unit (layout.prepared default.val signing).representation (layout.post default.val signing).representation
      (cachedDenote layout default signing P comparison comparisonCorrect drawSource)
      (cacheCall layout default signing P comparison comparisonCorrect port draw) := by
  have retained := (EncodedCacheRead.refines layout.cache P comparison comparisonCorrect port drawSource draw drawCorrect).retain
    (by decide) (layout.input default.val signing).representation layout.cache.wordFits
    (layout.prepared default.val signing).representation.fits (layout.post default.val signing).representation.fits
  have viewed := (retained.viewInput (layout.prepared default.val signing).representation
    (productView layout.cache.input (layout.input default.val signing)) (fun _ => rfl)).viewOutput
      (layout.post default.val signing).representation
      (productView (CacheRead.output layout.cache) (layout.input default.val signing)).symm (by
        intro value
        exact congrArg ((CacheRead.output layout.cache).representation.prod (layout.input default.val signing).representation
          (layout.post default.val signing).representation.fits).encoding.encode
          ((productView (CacheRead.output layout.cache) (layout.input default.val signing)).apply_symm_apply value))
  convert viewed using 1
  · funext value
    dsimp only [cachedDenote, cachedValue, Layouts.post, Layouts.prepared, Layout.prod, Layout.Value, productView]
    simp only [Functor.map_map]
    rfl
  · rfl

variable {respond : val.Value base × C → G} (response : Implementation .unit layout.responseInput layout.point respond)
    {slots : Nat} (responseBuffers : response.program.code.memBound ≤ slots) (reserve : slots + 3 < 2 ^ w)

def code : Interactive.Code w :=
  .seq (.compute (prepare layout default signing).program.code)
    (.seq (cacheCall layout default signing P comparison comparisonCorrect port draw)
      (.compute (finish layout default signing response responseBuffers reserve).program.code))

def requestValue (value : (layout.input default.val signing).Value) : layout.cache.input.Value :=
  ⟨(value.val.1, default.val, value.val.2.2.1, ()), (cacheArguments layout default signing).preserves value.val value.property⟩

def completed (value : (layout.input default.val signing).Value) (answer : (CacheRead.output layout.cache).Value) : layout.output.Value :=
  ⟨finishValue respond signing (answer.val, value.val),
    (finish layout default signing response responseBuffers reserve).preserves _ ⟨answer.property, value.property⟩⟩

def denote (drawSource : ProbComp layout.cache.value.Value) (value : (layout.input default.val signing).Value) : ProbComp layout.output.Value :=
  completed layout default signing response responseBuffers reserve value <$>
    EncodedCacheRead.denote layout.cache P comparison comparisonCorrect drawSource (requestValue layout default signing value)

theorem refines (drawSource : ProbComp layout.cache.value.Value)
    (drawCorrect : Interactive.Refines port .unit layout.cache.lookup.unit.representation layout.cache.value.representation
      (fun _ => drawSource) draw) :
    Interactive.Refines port .unit (layout.input default.val signing).representation layout.output.representation
      (denote layout default signing P comparison comparisonCorrect response responseBuffers reserve drawSource)
      (code layout default signing P comparison comparisonCorrect port draw response responseBuffers reserve) := by
  have composed := (Interactive.Refines.compute port .unit (prepare layout default signing).program).seq
    ((cache_refines layout default signing P comparison comparisonCorrect port draw drawSource drawCorrect).seq
      (Interactive.Refines.compute port .unit (finish layout default signing response responseBuffers reserve).program))
  convert composed using 1
  · funext value
    simp only [pure_bind, cachedDenote, bind_pure_comp, Functor.map_map]
    rfl
  · rfl

variable [SampleableType (val.Value base)]

theorem denote_source (drawSource : ProbComp layout.cache.value.Value)
    (drawLaw : Subtype.val <$> drawSource = ($ᵗ (val.Value base) : ProbComp (val.Value base)))
    (value : (layout.input default.val signing).Value) :
    Subtype.val <$> denote layout default signing P comparison comparisonCorrect response responseBuffers reserve drawSource value =
      (fun out => (out.1, value.val.2.1, out.2)) <$>
        (LazyAGM.listReply signing (fun sample => respond (sample, value.val.2.1)) value.val.1).run (value.val.2.2.1, value.val.2.2.2) := by
  have original := BLSCache.denote_privateOracle layout.cache P comparison comparisonCorrect drawSource drawLaw
    (requestValue layout default signing value)
  have mapped := congrArg (fun computation : ProbComp (val.Value base × List (key.Value base × val.Value base)) =>
    (fun answer => finishValue respond signing (answer, value.val)) <$> computation) original
  simp only [denote, completed, requestValue, Functor.map_map, LazyAGM.listReply, StateT.run, finishValue] at mapped ⊢
  exact mapped

/-- Decode the complete executed reply, jointly with its stored configuration,
cache and transcript. The only sampling-law premise concerns the primitive draw. -/
theorem observe (drawSource : ProbComp layout.cache.value.Value)
    (drawCorrect : Interactive.Refines port .unit layout.cache.lookup.unit.representation layout.cache.value.representation
      (fun _ => drawSource) draw)
    (drawLaw : Subtype.val <$> drawSource = ($ᵗ (val.Value base) : ProbComp (val.Value base)))
    (tape : RandomTape w) (value : (layout.input default.val signing).Value) (before : State w)
    (holds : (layout.input default.val signing).representation.Holds value before) :
    (fun result => Subtype.val <$> Interactive.observe layout.output.representation result) <$>
      (code layout default signing P comparison comparisonCorrect port draw response responseBuffers reserve).execute port .unit tape before =
        some <$> ((fun out => (out.1, value.val.2.1, out.2)) <$>
          (LazyAGM.listReply signing (fun sample => respond (sample, value.val.2.1)) value.val.1).run (value.val.2.2.1, value.val.2.2.2)) := by
  have observed := (refines layout default signing P comparison comparisonCorrect port draw response responseBuffers reserve
    drawSource drawCorrect).observe tape value before holds
  have mapped := congrArg (fun computation : ProbComp (Option layout.output.Value) =>
    (fun result => Subtype.val <$> result) <$> computation) observed
  rw [← denote_source layout default signing P comparison comparisonCorrect response responseBuffers reserve drawSource drawLaw value]
  have middle : (fun result => Subtype.val <$> result) <$> some <$>
      denote layout default signing P comparison comparisonCorrect response responseBuffers reserve drawSource value =
        some <$> Subtype.val <$> denote layout default signing P comparison comparisonCorrect response responseBuffers reserve drawSource value :=
    (PFunctor.FreeM.comp_map _ _ _).symm.trans
      (PFunctor.FreeM.comp_map some Subtype.val _)
  exact (PFunctor.FreeM.comp_map _ _ _).trans (mapped.trans middle)

end Signatures.Runtime.CaliperBackend.BLSReply
