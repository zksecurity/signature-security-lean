import Signatures.Runtime.Caliper.CoronTerminalArithmeticBounds
import Signatures.Runtime.CoronFinalCache

/-! Executed terminal cache read and co-CDH extraction. The cache request
admits hits at full capacity and fresh messages only when room remains. All
retention and extraction instructions are constructed from primitive code. -/
namespace Signatures.Runtime.CaliperBackend.CoronTerminal
open Caliper BoundedSource OracleComp OracleSpec
variable {w randomBound : Nat} {qS : Fin (randomBound + 1)} {M F G : Type}
    (layout : CoronService.Layouts w M F G randomBound qS)

structure Arithmetic [SMul F G] [Sub G] where
  scale : Implementation .unit layout.response.scaleArgs layout.point (fun value => value.1 • value.2)
  sub : Implementation .unit layout.response.points layout.point (fun value => value.1 - value.2)
  scaleTime : Nat
  scaleWords : Nat
  subTime : Nat
  subWords : Nat
  scaleBound : scale.BoundedBy scaleTime scaleWords
  subBound : sub.BoundedBy subTime subWords
  slots : Nat
  scaleNames : NamesBound scale.program.code slots
  subNames : NamesBound sub.program.code slots
  reserve : slots + 3 < 2 ^ w

variable [DecidableEq M]
theorem inputSize : layout.service.cache.input.representation.encoding.words +
    layout.response.points.representation.encoding.words ≤ width layout := by
  change layout.service.cache.lookup.input.representation.encoding.words + _ ≤ _
  rw [LookupLayout.input_words]
  change _ + (layout.point.representation.encoding.words + layout.point.representation.encoding.words) ≤ _
  unfold width
  omega
def input : Layout w (CacheLayout.Input M (F × Fin (qS.val + 1)) × (G × G)) :=
  layout.service.cache.input.prod layout.response.points
    (fits_of_le layout ((inputSize layout).trans (by omega)))

variable [SampleableType F] (sampler : CoronService.Sampler layout)
def readCode : Interactive.Code w :=
  CoronCache.code layout.cache randomBound layout.randomFits qS layout.pairFits sampler.code
def readSource : layout.service.cache.input.Value → ProbComp (CacheRead.output layout.service.cache).Value :=
  CoronCache.source layout.cache randomBound layout.randomFits qS layout.pairFits sampler.source
theorem read_refines : Interactive.Refines layout.port .unit layout.service.cache.input.representation
    (CacheRead.output layout.service.cache).representation (readSource layout sampler) (readCode layout sampler) :=
  CoronCache.refines layout.cache randomBound layout.randomFits qS layout.pairFits sampler.correct

def request (value : (input layout).Value) : layout.service.cache.input.Value :=
  (productView layout.service.cache.input layout.response.points value).1
def retainedValue (value : (input layout).Value) (answer : (CacheRead.output layout.service.cache).Value) :
    (returned layout).Value :=
  (productView (CacheRead.output layout.service.cache) layout.response.points).symm
    (answer, (productView layout.service.cache.input layout.response.points value).2)
def retainedSource (value : (input layout).Value) : ProbComp (returned layout).Value :=
  retainedValue layout value <$> readSource layout sampler (request layout value)
def retainedCode : Interactive.Code w :=
  Interactive.retain (readCode layout sampler) (Interactive.savedBuffer layout.port (readCode layout sampler))
    layout.service.cache.input.representation.encoding.words
    (CacheRead.output layout.service.cache).representation.encoding.words layout.response.points.representation.encoding.words
theorem retained_refines : Interactive.Refines layout.port .unit (input layout).representation (returned layout).representation
    (retainedSource layout sampler) (retainedCode layout sampler) := by
  have retained := (read_refines layout sampler).retain (by decide) layout.response.points.representation
    layout.cache.wordFits (input layout).representation.fits (returned layout).representation.fits
  have viewed := (retained.viewInput (input layout).representation
    (productView layout.service.cache.input layout.response.points) (fun _ => rfl)).viewOutput
      (returned layout).representation (productView (CacheRead.output layout.service.cache) layout.response.points).symm
      (by
        intro value
        exact congrArg
          ((CacheRead.output layout.service.cache).representation.prod layout.response.points.representation
            (returned layout).representation.fits).encoding.encode
            ((productView (CacheRead.output layout.service.cache) layout.response.points).apply_symm_apply value))
  convert viewed using 1
  · funext value
    exact PFunctor.FreeM.comp_map _ _ _
  · rfl

variable [SMul F G] [Sub G] (arithmetic : Arithmetic layout)
def extracted (value : (returned layout).Value) : layout.point.Value :=
  ⟨value.val.2.1 - value.val.1.1.1 • value.val.2.2,
    (extract layout arithmetic.scale arithmetic.scaleNames.buffers arithmetic.reserve arithmetic.sub).preserves value.val value.property⟩
def denote (value : (input layout).Value) : ProbComp layout.point.Value :=
  extracted layout arithmetic <$> retainedSource layout sampler value
def code : Interactive.Code w :=
  .seq (retainedCode layout sampler)
    (.compute (extract layout arithmetic.scale arithmetic.scaleNames.buffers arithmetic.reserve arithmetic.sub).program.code)
theorem refines : Interactive.Refines layout.port .unit (input layout).representation layout.point.representation
    (denote layout sampler arithmetic) (code layout sampler arithmetic) := by
  convert (retained_refines layout sampler).seq
    (Interactive.Refines.compute layout.port .unit
      (extract layout arithmetic.scale arithmetic.scaleNames.buffers arithmetic.reserve arithmetic.sub).program) using 1
  · funext value
    simp only [bind_pure_comp]
    rfl
  · rfl

theorem source_eq (value : (input layout).Value) :
    Subtype.val <$> denote layout sampler arithmetic value =
      (fun result => value.val.2.1 - result.1.1 • value.val.2.2) <$>
        ((BLS.LazyAGM.Reduction.privateListOracle (M := M) (R := F × Fin (qS.val + 1)))
          (.inr value.val.1.1)).run value.val.1.2.2.1 := by
  have read := CoronCache.source_eq layout.cache randomBound layout.randomFits qS layout.pairFits sampler.law (request layout value)
  change Subtype.val <$> readSource layout sampler (request layout value) =
    ((BLS.LazyAGM.Reduction.privateListOracle (M := M) (R := F × Fin (qS.val + 1)))
      (.inr value.val.1.1)).run value.val.1.2.2.1 at read
  rw [← read]
  simp only [denote, retainedSource, Functor.map_map]
  rfl

end Signatures.Runtime.CaliperBackend.CoronTerminal
