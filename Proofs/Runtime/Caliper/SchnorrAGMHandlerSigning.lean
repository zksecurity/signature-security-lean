import Proofs.Runtime.Caliper.SchnorrAGMHandlerSigningFinish
import Proofs.Runtime.Caliper.SchnorrAGMSigningDispatchBuffers

/-! Signing over the common store, retaining the runtime generator/public key
in actual Caliper storage across both draws and all signing-state updates. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Handler.SigningComponent
open Caliper BoundedSource OracleComp OracleSpec
variable {w qH qS randomBound : Nat} {M F G I : Type}
    [Zero F] [SMul F G] [Sub G] [Neg F] [DecidableEq M] [DecidableEq G]
    {spec : OracleSpec I} (layout : Handler.Layouts w M F G qH qS randomBound)
    (zeroValid : layout.scheme.scalar.valid 0)
    (scale : Implementation .unit layout.arithmetic.arithmetic.scaleArgs layout.scheme.point (fun args => args.1 • args.2))
    (sub : Implementation .unit layout.arithmetic.arithmetic.points layout.scheme.point (fun args => args.1 - args.2))
    (negate : Implementation .unit layout.scheme.scalar layout.scheme.scalar Neg.neg)
    {slots : Nat} (scaleBuffers : scale.program.code.memBound ≤ slots)
    (subBuffers : sub.program.code.memBound ≤ slots) (negateBuffers : negate.program.code.memBound ≤ slots)
    (reserve : slots + 4 < 2 ^ w) (port : Interactive.Port w spec)

def retained (sampler : Interactive.Code w) : Interactive.Code w :=
  let core := SigningDispatch.code layout.signing zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve port sampler
  Interactive.retain core (Interactive.savedBuffer port core)
    layout.signing.input.representation.encoding.words layout.signing.output.representation.encoding.words
    layout.scheme.config.representation.encoding.words
def code (sampler : Interactive.Code w) : Interactive.Code w := .seq (.compute (prepare layout).code)
  (.seq (retained layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve port sampler)
    (.compute (finish layout).code))
def source (sampler : OracleComp spec layout.scheme.scalar.Value) (args : layout.signingInput.Value) :
    OracleComp spec layout.scalarOutput.Value :=
  (fun answer => finishValue layout (answer, requestConfig layout args)) <$>
    SigningDispatch.source layout.signing zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve sampler
      (layout.signingValue args)

theorem retained_refines {sampler : Interactive.Code w} {sampleSource : OracleComp spec layout.scheme.scalar.Value}
    (sampleCorrect : Interactive.Refines port .unit (PairSampling.input w).representation layout.scheme.scalar.representation
      (fun _ => sampleSource) sampler) :
    Interactive.Refines port .unit layout.signingPrepared layout.signingFinished
      (fun args => (fun answer => (answer, args.2)) <$>
        SigningDispatch.source layout.signing zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve sampleSource args.1)
      (retained layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve port sampler) :=
  (SigningDispatch.refines layout.signing zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve port sampleCorrect).retain
    (by decide) layout.scheme.config.representation layout.scheme.wordFits layout.signingInputFits layout.signingOutputFits
theorem refines {sampler : Interactive.Code w} {sampleSource : OracleComp spec layout.scheme.scalar.Value}
    (sampleCorrect : Interactive.Refines port .unit (PairSampling.input w).representation layout.scheme.scalar.representation
      (fun _ => sampleSource) sampler) :
    Interactive.Refines port .unit layout.signingInput.representation layout.scalarOutput.representation
      (source layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve sampleSource)
      (code layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve port sampler) := by
  have combined := (Interactive.Refines.compute port .unit (prepare layout)).seq
    ((retained_refines layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve port sampleCorrect).seq
      (Interactive.Refines.compute port .unit (finish layout)))
  convert combined using 1
  · funext args
    simp only [pure_bind, bind_pure_comp]
    rw [Functor.map_map]
    rfl
  · rfl

theorem erase (sampler : OracleComp spec layout.scheme.scalar.Value) (args : layout.signingInput.Value) :
    Subtype.val <$> source layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve sampler args =
      (fun answer => (answer.val.1, args.val.2.1, answer.val.2)) <$>
        SigningDispatch.source layout.signing zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve sampler
          (layout.signingValue args) := by
  unfold source
  rw [Functor.map_map]
  rfl
theorem reply_config (sampler : OracleComp spec layout.scheme.scalar.Value) (args : layout.signingInput.Value)
    (answer : layout.scalarOutput.Value)
    (supported : answer ∈ support (source layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve sampler args)) :
    answer.val.2.1 = args.val.2.1 := by
  unfold source at supported
  rw [support_map] at supported
  obtain ⟨result, _, rfl⟩ := supported
  rfl

end Signatures.Runtime.CaliperBackend.SchnorrAGM.Handler.SigningComponent
