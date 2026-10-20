import Signatures.Runtime.Caliper.SchnorrAGMExtractionArithmeticBounds
import Signatures.Runtime.Caliper.SchnorrAGMEntryReadMemory
import Signatures.Runtime.Caliper.ReorderTail

/-! The terminal cache read followed by scalar extraction. The response scalar
is copied across the interactive read; the resulting private state is retained
across the constructed arithmetic. There is exactly one cache access. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.ExtractionRead
open Caliper BoundedSource OracleComp OracleSpec
open Signatures.Runtime.SchnorrAGM.Native
variable {w qH qS : Nat} {M F G : Type} (layout : Layouts w M F G qH qS)

theorem frameFits : layout.entry.representation.encoding.words + layout.state.representation.encoding.words +
    layout.scalar.representation.encoding.words < 2 ^ w :=
  layout.fits_of_le (by
    have entry := EntryRead.output_size layout
    change layout.entry.representation.encoding.words + layout.state.representation.encoding.words ≤ _ at entry
    have scalar := (ExtractionArithmetic.sizes layout).2
    omega)
def returned : Representation w ((EntryRead.output layout).Value × layout.scalar.Value) :=
  (EntryRead.output layout).representation.prod layout.scalar.representation (frameFits layout)
def arithmeticFrame : Representation w ((ExtractionArithmetic.input layout).Value × layout.state.Value) :=
  (ExtractionArithmetic.input layout).representation.prod layout.state.representation (by
    change (layout.entry.representation.encoding.words + layout.scalar.representation.encoding.words) + _ < _
    have := frameFits layout
    omega)

def arguments (value : (EntryRead.output layout).Value × layout.scalar.Value) :
    (ExtractionArithmetic.input layout).Value × layout.state.Value :=
  (⟨(value.1.val.1, value.2.val), value.1.property.1, value.2.property⟩, ⟨value.1.val.2, value.1.property.2⟩)
def prepare : Realizer .unit (returned layout) (arithmeticFrame layout) (arguments layout) :=
  ((ReorderTail.realizer layout.entry.representation layout.state.representation layout.scalar.representation
    layout.wordFits (frameFits layout)).viewInput (returned layout)
      (fun value => ((⟨value.1.val.1, value.1.property.1⟩, ⟨value.1.val.2, value.1.property.2⟩), value.2))
      (fun _ => rfl)).viewOutput (arithmeticFrame layout) (arguments layout) (fun _ => rfl)

variable [Zero F] [DecidableEq M] [DecidableEq G]

def input : Layout w (Read.RawInput (M := M) (F := F) (G := G) × F) :=
  (Read.input layout).prod layout.scalar (layout.fits_of_le (by
    have := (Read.sizes layout).1
    have := (ExtractionArithmetic.sizes layout).2
    omega))
def readInput (value : (input layout).Value) : (Read.input layout).Value := ⟨value.val.1, value.property.1⟩
def response (value : (input layout).Value) : layout.scalar.Value := ⟨value.val.2, value.property.2⟩

variable [Add F] [Sub F] [Div F] [DecidableEq F]
    (zeroValid : layout.scalar.valid 0)
    (add : Implementation .unit layout.affine layout.scalar (fun value => value.1 + value.2))
    (sub : Implementation .unit layout.affine layout.scalar (fun value => value.1 - value.2))
    (divide : Implementation .unit layout.affine layout.scalar (fun value => value.1 / value.2))
    {slots : Nat} (addBuffers : add.program.code.memBound ≤ slots) (subBuffers : sub.program.code.memBound ≤ slots)
    (divBuffers : divide.program.code.memBound ≤ slots) (reserve : slots + 3 < 2 ^ w)


def solution (value : (ExtractionArithmetic.input layout).Value × layout.state.Value) : (Read.output layout).Value :=
  ⟨(ExtractionArithmetic.value value.1.val, value.2.val),
    (ExtractionArithmetic.implementation layout add sub divide addBuffers subBuffers reserve zeroValid).preserves value.1.val value.1.property,
    value.2.property⟩

include divBuffers in
omit [DecidableEq F] [DecidableEq M] [DecidableEq G] in
theorem arithmetic_nameFits :
    (ExtractionArithmetic.implementation layout add sub divide addBuffers subBuffers reserve zeroValid).program.savedBuffer < 2 ^ w := by
  have bound := ExtractionArithmetic.buffers layout add sub divide addBuffers subBuffers reserve zeroValid divBuffers
  have hw := layout.wordFits
  change max 2 (ExtractionArithmetic.implementation layout add sub divide addBuffers subBuffers reserve zeroValid).program.code.memBound < _
  omega

def arithmetic : Realizer .unit (arithmeticFrame layout) (Read.output layout).representation
    (solution layout zeroValid add sub divide addBuffers subBuffers reserve) :=
  ((ExtractionArithmetic.implementation layout add sub divide addBuffers subBuffers reserve zeroValid).program.retain
    (by decide) layout.state.representation layout.wordFits
    (arithmetic_nameFits layout zeroValid add sub divide addBuffers subBuffers divBuffers reserve)
    (arithmeticFrame layout).fits (Read.output layout).representation.fits).viewOutput _
      (solution layout zeroValid add sub divide addBuffers subBuffers reserve) (fun _ => rfl)

def finish : Realizer .unit (returned layout) (Read.output layout).representation
    (fun value => solution layout zeroValid add sub divide addBuffers subBuffers reserve (arguments layout value)) :=
  (prepare layout).then (arithmetic layout zeroValid add sub divide addBuffers subBuffers divBuffers reserve)

variable {I : Type} {spec : OracleSpec I} (port : Interactive.Port w spec)
def read (sampler : Interactive.Code w) : Interactive.Code w :=
  Interactive.retain (EntryRead.code layout zeroValid add addBuffers ((Nat.le_add_right slots 3).trans_lt reserve) port sampler)
    (Interactive.savedBuffer port (EntryRead.code layout zeroValid add addBuffers ((Nat.le_add_right slots 3).trans_lt reserve) port sampler))
    (Read.input layout).representation.encoding.words (EntryRead.output layout).representation.encoding.words
    layout.scalar.representation.encoding.words
def code (sampler : Interactive.Code w) : Interactive.Code w :=
  .seq (read layout zeroValid add addBuffers reserve port sampler)
    (.compute (finish layout zeroValid add sub divide addBuffers subBuffers divBuffers reserve).code)
def source (sampler : OracleComp spec layout.scalar.Value) (value : (input layout).Value) :
    OracleComp spec (Read.output layout).Value :=
  (fun result => solution layout zeroValid add sub divide addBuffers subBuffers reserve
    (arguments layout (result, response layout value))) <$>
      EntryRead.source layout zeroValid sampler (readInput layout value)

omit [Sub F] [Div F] in
theorem read_refines {sampler : Interactive.Code w} {sampleSource : OracleComp spec layout.scalar.Value}
    (sampleCorrect : Interactive.Refines port .unit (PairSampling.input w).representation layout.scalar.representation
      (fun _ => sampleSource) sampler) :
    Interactive.Refines port .unit (input layout).representation (returned layout)
      (fun value => (fun result => (result, response layout value)) <$> EntryRead.source layout zeroValid sampleSource (readInput layout value))
      (read layout zeroValid add addBuffers reserve port sampler) :=
  ((EntryRead.refines layout zeroValid add addBuffers ((Nat.le_add_right slots 3).trans_lt reserve) port sampleCorrect).retain (by decide)
    layout.scalar.representation layout.wordFits (input layout).representation.fits (returned layout).fits).viewInput
      (input layout).representation (fun value => (readInput layout value, response layout value)) (fun _ => rfl)

theorem refines {sampler : Interactive.Code w} {sampleSource : OracleComp spec layout.scalar.Value}
    (sampleCorrect : Interactive.Refines port .unit (PairSampling.input w).representation layout.scalar.representation
      (fun _ => sampleSource) sampler) :
    Interactive.Refines port .unit (input layout).representation (Read.output layout).representation
      (source layout zeroValid add sub divide addBuffers subBuffers reserve sampleSource)
      (code layout zeroValid add sub divide addBuffers subBuffers divBuffers reserve port sampler) := by
  have combined := (read_refines layout zeroValid add addBuffers reserve port sampleCorrect).seq
    (Interactive.Refines.compute port .unit (finish layout zeroValid add sub divide addBuffers subBuffers divBuffers reserve))
  convert combined using 1
  · funext value
    simp only [bind_pure_comp, Functor.map_map, source]
  · rfl

end Signatures.Runtime.CaliperBackend.SchnorrAGM.ExtractionRead
