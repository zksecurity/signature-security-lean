import Proofs.Runtime.Caliper.SchnorrAGMFreshArithmeticBounds
import Proofs.Runtime.Caliper.PairSamplingBounds
import Proofs.Runtime.BackendSchnorrAGMFresh

/-! Fresh Schnorr entries from an executed scalar sampler and field addition.
The explanation and old bad flag survive the oracle call in charged storage. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Fresh
open Caliper BoundedSource OracleComp OracleSpec
variable {w qH qS : Nat} {M F G I : Type} [Zero F] [Add F] [DecidableEq F]
    {spec : OracleSpec I} (layout : Layouts w M F G qH qS)
    (zeroValid : layout.scalar.valid 0)
    (add : Implementation .unit layout.affine layout.scalar (fun value => value.1 + value.2))
    {slots : Nat} (addBuffers : add.program.code.memBound ≤ slots) (slotsFit : slots < 2 ^ w)
    (port : Interactive.Port w spec)

def sample (sampler : Interactive.Code w) : Interactive.Code w :=
  Interactive.retain sampler (Interactive.savedBuffer port sampler) 0
    layout.scalar.representation.encoding.words (Cache.saved layout).representation.encoding.words

def code (sampler : Interactive.Code w) : Interactive.Code w :=
  .seq (sample layout port sampler) (.compute (arithmetic layout zeroValid add addBuffers slotsFit).code)

def denote (source : OracleComp spec layout.scalar.Value) (state : (Cache.saved layout).Value) :
    OracleComp spec (layout.entry.Value × (Cache.saved layout).Value) :=
  (fun challenge => Cache.freshValue layout challenge state) <$> source

variable {source : OracleComp spec layout.scalar.Value} {sampler : Interactive.Code w}
    (sampleCorrect : Interactive.Refines port .unit (PairSampling.input w).representation layout.scalar.representation
      (fun _ => source) sampler)

include sampleCorrect in
omit [Zero F] [Add F] [DecidableEq F] in
theorem sample_refines : Interactive.Refines port .unit (Cache.saved layout).representation (input layout)
    (fun state => (fun challenge => (challenge, state)) <$> source) (sample layout port sampler) := by
  have retained := sampleCorrect.retain (by decide) (Cache.saved layout).representation layout.wordFits
    (by change 0 + _ < _; simpa using (Cache.saved layout).representation.fits) (input layout).fits
  exact retained.viewInput (Cache.saved layout).representation (fun state => (⟨(), trivial⟩, state)) (fun _ => rfl)

include sampleCorrect in
theorem refines : Interactive.Refines port .unit (Cache.saved layout).representation (Cache.model layout).freshOutput
    (denote layout source) (code layout zeroValid add addBuffers slotsFit port sampler) := by
  have combined := (sample_refines layout port sampleCorrect).seq
    (Interactive.Refines.compute port .unit (arithmetic layout zeroValid add addBuffers slotsFit))
  have sourceEq (state : (Cache.saved layout).Value) :
      (do let value ← (fun challenge => (challenge, state)) <$> source
          pure (Cache.freshValue layout value.1 value.2)) = denote layout source state := by
    simp only [denote, bind_pure_comp, Functor.map_map]
  intro tape state before holds
  change Synchronizes _ (denote layout source state) _
  rw [← sourceEq state]
  exact combined tape state before holds

section Original
variable {w qH qS : Nat} {M F G I : Type} [Field F] [DecidableEq F]
    {spec : OracleSpec I} (layout : Layouts w M F G qH qS)

theorem source_value (source : OracleComp spec layout.scalar.Value) (state : (Cache.saved layout).Value) :
    (fun result => (result.1.val, result.2.val)) <$> denote layout source state =
      (fun challenge => Signatures.Runtime.SchnorrAGM.Native.freshValue (challenge, state.val)) <$>
        (Subtype.val <$> source) := by
  simp only [denote, Functor.map_map]
  rfl

theorem source_uniform [SampleableType F] (source : ProbComp layout.scalar.Value)
    (law : Subtype.val <$> source = ($ᵗ F : ProbComp F)) (state : (Cache.saved layout).Value) :
    (fun result => (result.1.val, result.2.val)) <$> denote layout source state =
      (fun challenge => Signatures.Runtime.SchnorrAGM.Native.freshValue (challenge, state.val)) <$> ($ᵗ F : ProbComp F) := by
  rw [source_value, law]

end Original
end Signatures.Runtime.CaliperBackend.SchnorrAGM.Fresh
