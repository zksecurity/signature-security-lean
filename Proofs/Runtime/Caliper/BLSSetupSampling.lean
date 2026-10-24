import Proofs.Runtime.Caliper.BLSSetupNames
import Proofs.Runtime.Caliper.SynchronizesObservations

/-! The bad BLS setup draws its scalar through an actual sampler while retaining
the input challenge. Its source law follows from the sampler's uniform law and
the proved local setup, not a completed reduction implementation contract. -/

namespace Signatures.Runtime.CaliperBackend.BLSSetup
open Caliper BoundedSource OracleComp OracleSpec

variable {w : Nat} {M F G K : Type} (layout : Layouts w M F G K)
    (port : Interactive.Port w unifSpec)

def goodCode : Interactive.Code w := .compute (good layout).program.code

theorem good_observe (tape : RandomTape w) (value : layout.challenge.Value) (before : State w)
    (holds : layout.challenge.representation.Holds value before) :
    (fun result => Subtype.val <$> Interactive.observe layout.goodOutput.representation result) <$>
      (goodCode layout).execute port .unit tape before = pure (some (value.val.2.2, value.val.1, [], [], [])) := by
  have observed := (Interactive.Refines.compute port .unit (good layout).program).observe tape value before holds
  have erased := congrArg (fun computation => (fun result => Subtype.val <$> result) <$> computation) observed
  simp only [Functor.map_map, map_pure] at erased
  convert erased using 1 <;> rfl

variable (draw : Interactive.Code w) (drawSource : ProbComp layout.scheme.cache.value.Value)

def sample : Interactive.Code w := Interactive.retain draw (Interactive.savedBuffer port draw) 0
  layout.scheme.cache.value.representation.encoding.words layout.challenge.representation.encoding.words

def sampledValue (value : layout.challenge.Value) (scalar : layout.scheme.cache.value.Value) : layout.sampled.Value :=
  ⟨(scalar.val, value.val), scalar.property, value.property⟩

variable (drawCorrect : Interactive.Refines port .unit layout.scheme.cache.lookup.unit.representation
    layout.scheme.cache.value.representation (fun _ => drawSource) draw)

include drawCorrect in
theorem sample_refines : Interactive.Refines port .unit layout.challenge.representation layout.sampled.representation
    (fun value => sampledValue layout value <$> drawSource) (sample layout port draw) := by
  have saved := drawCorrect.retain (by decide) layout.challenge.representation layout.scheme.cache.wordFits
    (by change 0 + layout.challenge.representation.encoding.words < 2 ^ w; simpa only [Nat.zero_add] using layout.challenge.representation.fits)
    layout.sampled.representation.fits
  have input := saved.viewInput layout.challenge.representation (fun value => (⟨(), trivial⟩, value)) (fun _ => rfl)
  have output := input.viewOutput layout.sampled.representation
    (fun value => ⟨(value.1.val, value.2.val), value.1.property, value.2.property⟩) (fun _ => rfl)
  simp only [LookupLayout.unit_words, Functor.map_map] at output
  convert output using 1
  · funext value
    rfl
  · rfl

variable [SMul F K]
    (scale : Implementation .unit layout.scaleArgs layout.key (fun value => value.1 • value.2))
    {slots : Nat} (scaleBuffers : scale.program.code.memBound ≤ slots) (reserve : slots + 4 < 2 ^ w)

def badCode : Interactive.Code w :=
  .seq (sample layout port draw) (.compute (badLocal layout scale scaleBuffers reserve).program.code)

def badResult (value : layout.sampled.Value) : layout.badOutput.Value :=
  ⟨(value.val.1 • value.val.2.2.1, (value.val.1, value.val.2.1), [], [], []),
    (badLocal layout scale scaleBuffers reserve).preserves value.val value.property⟩

def badSource (value : layout.challenge.Value) : ProbComp layout.badOutput.Value :=
  (fun scalar => badResult layout scale scaleBuffers reserve (sampledValue layout value scalar)) <$> drawSource

include drawCorrect in
theorem bad_refines : Interactive.Refines port .unit layout.challenge.representation layout.badOutput.representation
    (badSource layout drawSource scale scaleBuffers reserve) (badCode layout port draw scale scaleBuffers reserve) := by
  have composed := (sample_refines layout port draw drawSource drawCorrect).seq
    (Interactive.Refines.compute port .unit (badLocal layout scale scaleBuffers reserve).program)
  simp only [bind_pure_comp, Functor.map_map] at composed
  convert composed using 1
  · funext value
    rfl
  · rfl

theorem badSource_reserved (remaining : Nat) (cacheRoom : remaining ≤ layout.scheme.cache.capacityPred + 1)
    (logRoom : remaining ≤ layout.scheme.capacityPred + 1) (value : layout.challenge.Value)
    (answer : layout.badOutput.Value) (supported : answer ∈ support (badSource layout drawSource scale scaleBuffers reserve value)) :
    BLSReply.Reserved layout.scheme.bad remaining answer.val.2 := by
  obtain ⟨sampled, _, rfl⟩ := (show ∃ sampled ∈ support drawSource,
      badResult layout scale scaleBuffers reserve (sampledValue layout value sampled) = answer from by
    simpa only [badSource, support_map, Set.mem_image] using supported)
  exact bad_reserved layout remaining cacheRoom logRoom (sampledValue layout value sampled)

variable [SampleableType F]
    (drawLaw : Subtype.val <$> drawSource = ($ᵗ F : ProbComp F))

include drawLaw in
theorem badSource_uniform (value : layout.challenge.Value) :
    Subtype.val <$> badSource layout drawSource scale scaleBuffers reserve value =
      (fun scalar => (scalar • value.val.2.1, (scalar, value.val.1), [], [], [])) <$> ($ᵗ F : ProbComp F) := by
  rw [← drawLaw]
  simp only [badSource, Functor.map_map]
  rfl

include drawCorrect drawLaw in
theorem bad_observe (tape : RandomTape w) (value : layout.challenge.Value) (before : State w)
    (holds : layout.challenge.representation.Holds value before) :
    (fun result => Subtype.val <$> Interactive.observe layout.badOutput.representation result) <$>
      (badCode layout port draw scale scaleBuffers reserve).execute port .unit tape before =
      (fun scalar => some (scalar • value.val.2.1, (scalar, value.val.1), [], [], [])) <$> ($ᵗ F : ProbComp F) := by
  have observed := (bad_refines layout port draw drawSource drawCorrect scale scaleBuffers reserve).observe tape value before holds
  have erased := congrArg (fun computation => (fun result => Subtype.val <$> result) <$> computation) observed
  have erased' :
      (fun result => Subtype.val <$> Interactive.observe layout.badOutput.representation result) <$>
        (badCode layout port draw scale scaleBuffers reserve).execute port .unit tape before =
        some <$> (Subtype.val <$> badSource layout drawSource scale scaleBuffers reserve value) := by
    simp only [Functor.map_map] at erased
    simp only [Functor.map_map]
    convert erased using 1
    rfl
  rw [badSource_uniform layout drawSource scale scaleBuffers reserve drawLaw value] at erased'
  simpa only [Functor.map_map] using erased'

end Signatures.Runtime.CaliperBackend.BLSSetup
