import Proofs.Runtime.Caliper.SchnorrAGMHandlerHashFinish

/-! Hash handling over the common store. The runtime configuration is retained
in a separate Caliper buffer while the all-shape hash core updates the state. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Handler.HashComponent
open Caliper BoundedSource OracleComp OracleSpec
variable {w qH qS randomBound : Nat} {M F G I : Type}
    [Zero F] [Mul F] [Add F] [DecidableEq F] [DecidableEq M] [DecidableEq G]
    {spec : OracleSpec I} (layout : Handler.Layouts w M F G qH qS randomBound)
    (zeroValid : layout.scheme.scalar.valid 0)
    (mul : Implementation .unit layout.scheme.affine layout.scheme.scalar (fun value => value.1 * value.2))
    (add : Implementation .unit layout.scheme.affine layout.scheme.scalar (fun value => value.1 + value.2))
    {slots : Nat} (mulBuffers : mul.program.code.memBound ≤ slots) (addBuffers : add.program.code.memBound ≤ slots)
    (reserve : slots + 4 < 2 ^ w) (port : Interactive.Port w spec)

def retained (sampler : Interactive.Code w) : Interactive.Code w :=
  let core := HashDispatch.code layout.hash zeroValid mul add mulBuffers addBuffers reserve port sampler
  Interactive.retain core (Interactive.savedBuffer port core)
    layout.hash.input.representation.encoding.words (Read.output layout.scheme).representation.encoding.words
    layout.scheme.config.representation.encoding.words
def code (sampler : Interactive.Code w) : Interactive.Code w := .seq (.compute (prepare layout).code)
  (.seq (retained layout zeroValid mul add mulBuffers addBuffers reserve port sampler) (.compute (finish layout).code))
def source (sampler : OracleComp spec layout.scheme.scalar.Value) (args : layout.hashInput.Value) :
    OracleComp spec layout.scalarOutput.Value :=
  (fun answer => finishValue layout (answer, requestConfig layout args)) <$>
    HashDispatch.source layout.hash zeroValid mul add mulBuffers addBuffers reserve sampler (layout.hashValue args)

theorem retained_refines {sampler : Interactive.Code w} {sampleSource : OracleComp spec layout.scheme.scalar.Value}
    (sampleCorrect : Interactive.Refines port .unit (PairSampling.input w).representation layout.scheme.scalar.representation
      (fun _ => sampleSource) sampler) :
    Interactive.Refines port .unit layout.hashPrepared layout.hashFinished
      (fun args => (fun answer => (answer, args.2)) <$>
        HashDispatch.source layout.hash zeroValid mul add mulBuffers addBuffers reserve sampleSource args.1)
      (retained layout zeroValid mul add mulBuffers addBuffers reserve port sampler) :=
  (HashDispatch.refines layout.hash zeroValid mul add mulBuffers addBuffers reserve port sampleCorrect).retain
    (by decide) layout.scheme.config.representation layout.scheme.wordFits layout.hashInputFits layout.hashOutputFits
theorem refines {sampler : Interactive.Code w} {sampleSource : OracleComp spec layout.scheme.scalar.Value}
    (sampleCorrect : Interactive.Refines port .unit (PairSampling.input w).representation layout.scheme.scalar.representation
      (fun _ => sampleSource) sampler) :
    Interactive.Refines port .unit layout.hashInput.representation layout.scalarOutput.representation
      (source layout zeroValid mul add mulBuffers addBuffers reserve sampleSource)
      (code layout zeroValid mul add mulBuffers addBuffers reserve port sampler) := by
  have combined := (Interactive.Refines.compute port .unit (prepare layout)).seq
    ((retained_refines layout zeroValid mul add mulBuffers addBuffers reserve port sampleCorrect).seq
      (Interactive.Refines.compute port .unit (finish layout)))
  convert combined using 1
  · funext args
    simp only [pure_bind, bind_pure_comp]
    rw [Functor.map_map]
    rfl
  · rfl

theorem erase (sampler : OracleComp spec layout.scheme.scalar.Value) (args : layout.hashInput.Value) :
    Subtype.val <$> source layout zeroValid mul add mulBuffers addBuffers reserve sampler args =
      (fun answer => ((answer.val.1, []), args.val.2.1, answer.val.2)) <$>
        HashDispatch.source layout.hash zeroValid mul add mulBuffers addBuffers reserve sampler (layout.hashValue args) := by
  unfold source
  rw [Functor.map_map]
  rfl
theorem reply_config (sampler : OracleComp spec layout.scheme.scalar.Value) (args : layout.hashInput.Value)
    (answer : layout.scalarOutput.Value)
    (supported : answer ∈ support (source layout zeroValid mul add mulBuffers addBuffers reserve sampler args)) :
    answer.val.1.2 = [] ∧ answer.val.2.1 = args.val.2.1 := by
  unfold source at supported
  rw [support_map] at supported
  obtain ⟨result, _, rfl⟩ := supported
  exact ⟨rfl, rfl⟩

end Signatures.Runtime.CaliperBackend.SchnorrAGM.Handler.HashComponent
