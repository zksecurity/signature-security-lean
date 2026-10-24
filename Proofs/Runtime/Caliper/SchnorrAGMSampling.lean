import Proofs.Runtime.Caliper.SchnorrAGMSampledBounds
import Proofs.Runtime.Caliper.PairSamplingBounds

/-! Complete accepted signing: draw the challenge, then the response, retain
the request/state during both draws, and execute the deterministic signing
program. The input reserves capacity independently of either sampled value. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Signing.Sampling
open Caliper BoundedSource OracleComp OracleSpec
open Signatures.Runtime.SchnorrAGM.Native
variable {w qH qS : Nat} {M F G I : Type} {spec : OracleSpec I}
    (layout : Histories.Layouts w M F G qH qS)

abbrev RequestState (M F G : Type) := G × G × M × EncodedState F G M
def ready (_layout : Histories.Layouts w M F G qH qS) (args : RequestState M F G) : Prop :=
  args.2.2.2.1.length ≤ qH + qS ∧ args.2.2.2.2.1.length < qS + 2 ∧ args.2.2.2.2.2.1.length < qS
instance readyDecidable : DecidablePred (ready layout) := by intro args; unfold ready; infer_instance
def input : Layout w (RequestState M F G) := layout.signing.base.restrict (ready layout)

theorem pairFits : layout.scheme.scalar.representation.encoding.words + layout.scheme.scalar.representation.encoding.words < 2 ^ w :=
  layout.scheme.affine.representation.fits
theorem frameFits : layout.scheme.affine.representation.encoding.words + (input layout).representation.encoding.words < 2 ^ w :=
  layout.signing.input.representation.fits

def pairs (port : Interactive.Port w spec) (sampler : Interactive.Code w) : Interactive.Code w :=
  PairSampling.code layout.scheme.scalar layout.scheme.scalar layout.scheme.wordFits (pairFits layout) port sampler sampler
def pairSource (sampler : OracleComp spec layout.scheme.scalar.Value) : OracleComp spec layout.scheme.affine.Value :=
  PairSampling.denote layout.scheme.scalar layout.scheme.scalar (pairFits layout) sampler sampler
def sample (port : Interactive.Port w spec) (sampler : Interactive.Code w) : Interactive.Code w :=
  Interactive.retain (pairs layout port sampler) (Interactive.savedBuffer port (pairs layout port sampler)) 0
    layout.scheme.affine.representation.encoding.words (input layout).representation.encoding.words

variable [Zero F] [SMul F G] [Sub G] [Neg F] [DecidableEq M] [DecidableEq G]

def sampleValue (args : layout.scheme.affine.Value × (input layout).Value) : (Sampled.input layout).Value :=
  ⟨(args.1.val, args.2.val), ⟨args.1.property, args.2.property.1⟩,
    args.2.property.2.2, fun _ => args.2.property.2.1⟩

def sampleSource (sampler : OracleComp spec layout.scheme.scalar.Value) (args : (input layout).Value) :
    OracleComp spec (Sampled.input layout).Value :=
  (fun pair => sampleValue layout (pair, args)) <$> pairSource layout sampler

theorem sample_refines (port : Interactive.Port w spec) {sampler : Interactive.Code w}
    {samplerSource : OracleComp spec layout.scheme.scalar.Value}
    (sampleCorrect : Interactive.Refines port .unit (PairSampling.input w).representation layout.scheme.scalar.representation
      (fun _ => samplerSource) sampler) :
    Interactive.Refines port .unit (input layout).representation (Sampled.input layout).representation
      (sampleSource layout samplerSource) (sample layout port sampler) := by
  have paired := PairSampling.refines (hw := layout.scheme.wordFits) (fits := pairFits layout) sampleCorrect sampleCorrect
  have retained := paired.retain (by decide) (input layout).representation layout.scheme.wordFits
    (by change 0 + _ < _; simpa using (input layout).representation.fits) (frameFits layout)
  have viewed := (retained.viewInput (input layout).representation (fun args => (⟨(), trivial⟩, args)) (fun _ => rfl)).viewOutput
    (Sampled.input layout).representation (sampleValue layout) (fun _ => rfl)
  convert viewed using 1
  · funext args
    exact PFunctor.FreeM.comp_map (sampleValue layout) (fun pair => (pair, args)) (pairSource layout samplerSource)
  · rfl

variable (zeroValid : layout.scheme.scalar.valid 0)
    (scale : Implementation .unit layout.signing.arithmetic.scaleArgs layout.scheme.point (fun args => args.1 • args.2))
    (sub : Implementation .unit layout.signing.arithmetic.points layout.scheme.point (fun args => args.1 - args.2))
    (negate : Implementation .unit layout.scheme.scalar layout.scheme.scalar Neg.neg)
    {slots : Nat} (scaleBuffers : scale.program.code.memBound ≤ slots)
    (subBuffers : sub.program.code.memBound ≤ slots) (negateBuffers : negate.program.code.memBound ≤ slots)
    (reserve : slots + 4 < 2 ^ w)

def code (port : Interactive.Port w spec) (sampler : Interactive.Code w) : Interactive.Code w :=
  .seq (sample layout port sampler)
    (.compute (Sampled.implementation layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve).program.code)

def denote (sampler : OracleComp spec layout.scheme.scalar.Value) (args : (input layout).Value) :
    OracleComp spec (Programming.output layout).Value :=
  (fun sampled => ⟨Sampled.value sampled.val,
    (Sampled.implementation layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve).preserves sampled.val sampled.property⟩) <$>
      sampleSource layout sampler args

theorem refines (port : Interactive.Port w spec) {sampler : Interactive.Code w}
    {samplerSource : OracleComp spec layout.scheme.scalar.Value}
    (sampleCorrect : Interactive.Refines port .unit (PairSampling.input w).representation layout.scheme.scalar.representation
      (fun _ => samplerSource) sampler) :
    Interactive.Refines port .unit (input layout).representation (Programming.output layout).representation
      (denote layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve samplerSource)
      (code layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve port sampler) := by
  have combined := (sample_refines layout port sampleCorrect).seq
    (Interactive.Refines.compute port .unit
      (Sampled.implementation layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve).program)
  convert combined using 1
  · funext args
    exact (bind_pure_comp _ _).symm
  · rfl

theorem erase {spec : OracleSpec.{0, 0} I} (sampler : OracleComp spec layout.scheme.scalar.Value) (args : (input layout).Value) :
    Subtype.val <$> denote layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve sampler args = (do
      let challenge ← Subtype.val <$> sampler
      let response ← Subtype.val <$> sampler
      pure (Sampled.value ((challenge, response), args.val))) := by
  have one := PFunctor.FreeM.comp_map Subtype.val
    (fun sampled : (Sampled.input layout).Value => (⟨Sampled.value sampled.val,
      (Sampled.implementation layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve).preserves sampled.val sampled.property⟩ :
        (Programming.output layout).Value)) (sampleSource layout sampler args)
  have two := PFunctor.FreeM.comp_map (fun sampled : (Sampled.input layout).Value => Sampled.value sampled.val)
    (fun pair => sampleValue layout (pair, args)) (pairSource layout sampler)
  have three := PFunctor.FreeM.comp_map (fun pair : F × F => Sampled.value (pair, args.val)) Subtype.val (pairSource layout sampler)
  have erased := PairSampling.erase layout.scheme.scalar layout.scheme.scalar (pairFits layout) sampler sampler
  have mapped := congrArg (fun computation : OracleComp spec (F × F) =>
    (fun pair => Sampled.value (pair, args.val)) <$> computation) erased
  refine one.symm.trans (two.symm.trans (three.trans (mapped.trans ?_)))
  simp only [map_bind, Functor.map_map, bind_pure_comp]

end Signatures.Runtime.CaliperBackend.SchnorrAGM.Signing.Sampling
