import Proofs.Runtime.Caliper.SchnorrAGMExtractionEntry
import Proofs.Runtime.Caliper.SchnorrAGMExtractionReadMemory

/-! Complete final-forgery scalar extraction: test shape, flatten coefficients,
read the first cached entry or lazily sample it, and compute its solution.
The response is physically saved across dispatch and the updated state across
arithmetic. Malformed shapes return zero and preserve the complete state. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Extraction
open Caliper BoundedSource OracleComp OracleSpec
variable {w qH qS : Nat} {M F G : Type} (layout : HashDispatch.Layouts w M F G qH qS)
    [DecidableEq M] [DecidableEq G]

def input : Layout w (HashDispatch.Input M F G × F) :=
  layout.input.prod layout.hash.scheme.scalar (layout.fits_of_le (by
    have := layout.input_le
    have := (ExtractionArithmetic.sizes layout.hash.scheme).2
    have := layout.hash.width_eq
    have := layout.parts
    omega))
def request (value : (input layout).Value) : layout.input.Value := ⟨value.val.1, value.property.1⟩
def response (value : (input layout).Value) : layout.hash.scheme.scalar.Value := ⟨value.val.2, value.property.2⟩

variable [Zero F] [Mul F] [Add F] [Sub F] [Div F] [DecidableEq F]
    (zeroValid : layout.hash.scheme.scalar.valid 0)
    (mul : Implementation .unit layout.hash.scheme.affine layout.hash.scheme.scalar (fun value => value.1 * value.2))
    (add : Implementation .unit layout.hash.scheme.affine layout.hash.scheme.scalar (fun value => value.1 + value.2))
    (sub : Implementation .unit layout.hash.scheme.affine layout.hash.scheme.scalar (fun value => value.1 - value.2))
    (divide : Implementation .unit layout.hash.scheme.affine layout.hash.scheme.scalar (fun value => value.1 / value.2))
    {slots : Nat} (mulBuffers : mul.program.code.memBound ≤ slots) (addBuffers : add.program.code.memBound ≤ slots)
    (subBuffers : sub.program.code.memBound ≤ slots) (divBuffers : divide.program.code.memBound ≤ slots)
    (reserve : slots + 4 < 2 ^ w)

include reserve in
omit [Zero F] [Mul F] [Add F] [Sub F] [Div F] [DecidableEq F] [DecidableEq M] [DecidableEq G] in
theorem arithmeticReserve : slots + 3 < 2 ^ w := (Nat.le_succ _).trans_lt reserve

def finish := ExtractionRead.finish layout.hash.scheme zeroValid add sub divide addBuffers subBuffers divBuffers
  (arithmeticReserve reserve)

variable {I : Type} {spec : OracleSpec I} (port : Interactive.Port w spec)
def read (sampler : Interactive.Code w) : Interactive.Code w :=
  Interactive.retain (ExtractionEntry.code layout zeroValid mul add mulBuffers addBuffers reserve port sampler)
    (Interactive.savedBuffer port (ExtractionEntry.code layout zeroValid mul add mulBuffers addBuffers reserve port sampler))
    layout.input.representation.encoding.words (EntryRead.output layout.hash.scheme).representation.encoding.words
    layout.hash.scheme.scalar.representation.encoding.words
def code (sampler : Interactive.Code w) : Interactive.Code w :=
  .seq (read layout zeroValid mul add mulBuffers addBuffers reserve port sampler)
    (.compute (finish layout zeroValid add sub divide addBuffers subBuffers divBuffers reserve).code)
def source (sampler : OracleComp spec layout.hash.scheme.scalar.Value) (value : (input layout).Value) :
    OracleComp spec (Read.output layout.hash.scheme).Value :=
  (fun result => ExtractionRead.solution layout.hash.scheme zeroValid add sub divide addBuffers subBuffers
    (arithmeticReserve reserve) (ExtractionRead.arguments layout.hash.scheme (result, response layout value))) <$>
      ExtractionEntry.source layout zeroValid mul add mulBuffers addBuffers reserve sampler (request layout value)

omit [Sub F] [Div F] in
theorem read_refines {sampler : Interactive.Code w} {sampleSource : OracleComp spec layout.hash.scheme.scalar.Value}
    (sampleCorrect : Interactive.Refines port .unit (PairSampling.input w).representation layout.hash.scheme.scalar.representation
      (fun _ => sampleSource) sampler) :
    Interactive.Refines port .unit (input layout).representation (ExtractionRead.returned layout.hash.scheme)
      (fun value => (fun result => (result, response layout value)) <$>
        ExtractionEntry.source layout zeroValid mul add mulBuffers addBuffers reserve sampleSource (request layout value))
      (read layout zeroValid mul add mulBuffers addBuffers reserve port sampler) :=
  ((ExtractionEntry.refines layout zeroValid mul add mulBuffers addBuffers reserve port sampleCorrect).retain (by decide)
    layout.hash.scheme.scalar.representation layout.hash.scheme.wordFits (input layout).representation.fits
    (ExtractionRead.returned layout.hash.scheme).fits).viewInput
      (input layout).representation (fun value => (request layout value, response layout value)) (fun _ => rfl)

theorem refines {sampler : Interactive.Code w} {sampleSource : OracleComp spec layout.hash.scheme.scalar.Value}
    (sampleCorrect : Interactive.Refines port .unit (PairSampling.input w).representation layout.hash.scheme.scalar.representation
      (fun _ => sampleSource) sampler) :
    Interactive.Refines port .unit (input layout).representation (Read.output layout.hash.scheme).representation
      (source layout zeroValid mul add sub divide mulBuffers addBuffers subBuffers reserve sampleSource)
      (code layout zeroValid mul add sub divide mulBuffers addBuffers subBuffers divBuffers reserve port sampler) := by
  have combined := (read_refines layout zeroValid mul add mulBuffers addBuffers reserve port sampleCorrect).seq
    (Interactive.Refines.compute port .unit (finish layout zeroValid add sub divide addBuffers subBuffers divBuffers reserve))
  convert combined using 1
  · funext value
    simp only [bind_pure_comp, Functor.map_map, source]
  · rfl

end Signatures.Runtime.CaliperBackend.SchnorrAGM.Extraction
