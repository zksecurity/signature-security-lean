import Signatures.Runtime.Caliper.SchnorrAGMHashAccept
import Signatures.Runtime.Caliper.SchnorrAGMExtractionReject

/-! The final-forgery entry dispatcher executes the singleton shape test and
coefficient flattening before its single cache read. Rejected forgeries return
an unexplained entry without changing state or requesting randomness. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.ExtractionEntry
open Caliper BoundedSource OracleComp OracleSpec
variable {w qH qS : Nat} {M F G I : Type} [Zero F] [Mul F] [Add F] [DecidableEq F] [DecidableEq M] [DecidableEq G]
    {spec : OracleSpec I} (layout : HashDispatch.Layouts w M F G qH qS) (zeroValid : layout.hash.scheme.scalar.valid 0)
    (mul : Implementation .unit layout.hash.scheme.affine layout.hash.scheme.scalar (fun value => value.1 * value.2))
    (add : Implementation .unit layout.hash.scheme.affine layout.hash.scheme.scalar (fun value => value.1 + value.2))
    {slots : Nat} (mulBuffers : mul.program.code.memBound ≤ slots) (addBuffers : add.program.code.memBound ≤ slots)
    (reserve : slots + 4 < 2 ^ w)

def prepare := (HashDispatch.accept layout).then (Hash.prepare layout.hash zeroValid mul add mulBuffers addBuffers reserve)
def rejected : Realizer .unit layout.no.representation (EntryRead.output layout.hash.scheme).representation
    (fun value => rejectValue layout zeroValid ⟨value.val, value.property.1⟩) :=
  (reject layout zeroValid).viewInput layout.no.representation (fun value => ⟨value.val, value.property.1⟩) (fun _ => rfl)

variable (port : Interactive.Port w spec)
def accepted (sampler : Interactive.Code w) : Interactive.Code w :=
  .seq (.compute (prepare layout zeroValid mul add mulBuffers addBuffers reserve).code)
    (EntryRead.code layout.hash.scheme zeroValid add addBuffers ((Nat.le_add_right slots 4).trans_lt reserve) port sampler)
def dispatch (sampler : Interactive.Code w) : Interactive.Code w :=
  Interactive.dispatch (accepted layout zeroValid mul add mulBuffers addBuffers reserve port sampler)
    (.compute (rejected layout zeroValid).code) layout.yes.representation.encoding.words layout.no.representation.encoding.words
def code (sampler : Interactive.Code w) : Interactive.Code w :=
  .seq (.compute (HashDispatch.selector layout).program.code) (dispatch layout zeroValid mul add mulBuffers addBuffers reserve port sampler)

def selectedValue (value : layout.input.Value) : layout.selected.Value :=
  ⟨GuardedBranch.select HashDispatch.shape value.val, (HashDispatch.selector layout).preserves value.val value.property⟩
def source (sampler : OracleComp spec layout.hash.scheme.scalar.Value) (value : layout.input.Value) :
    OracleComp spec (EntryRead.output layout.hash.scheme).Value :=
  Sum.elim
    (fun chosen => EntryRead.source layout.hash.scheme zeroValid sampler
      (Hash.prepareValue layout.hash zeroValid mul add mulBuffers addBuffers reserve (layout.acceptedValue chosen)))
    (fun chosen => pure (rejectValue layout zeroValid ⟨chosen.val, chosen.property.1⟩))
    (sumView layout.yes layout.no (selectedValue layout value))

theorem accepted_refines {sampler : Interactive.Code w} {sampleSource : OracleComp spec layout.hash.scheme.scalar.Value}
    (sampleCorrect : Interactive.Refines port .unit (PairSampling.input w).representation layout.hash.scheme.scalar.representation
      (fun _ => sampleSource) sampler) :
    Interactive.Refines port .unit layout.yes.representation (EntryRead.output layout.hash.scheme).representation
      (fun value => EntryRead.source layout.hash.scheme zeroValid sampleSource
        (Hash.prepareValue layout.hash zeroValid mul add mulBuffers addBuffers reserve (layout.acceptedValue value)))
      (accepted layout zeroValid mul add mulBuffers addBuffers reserve port sampler) := by
  have combined := (Interactive.Refines.compute port .unit (prepare layout zeroValid mul add mulBuffers addBuffers reserve)).seq
    (EntryRead.refines layout.hash.scheme zeroValid add addBuffers ((Nat.le_add_right slots 4).trans_lt reserve) port sampleCorrect)
  convert combined using 1
  · funext value
    simp only [pure_bind, Function.comp_apply]
  · rfl

theorem refines {sampler : Interactive.Code w} {sampleSource : OracleComp spec layout.hash.scheme.scalar.Value}
    (sampleCorrect : Interactive.Refines port .unit (PairSampling.input w).representation layout.hash.scheme.scalar.representation
      (fun _ => sampleSource) sampler) :
    Interactive.Refines port .unit layout.input.representation (EntryRead.output layout.hash.scheme).representation
      (source layout zeroValid mul add mulBuffers addBuffers reserve sampleSource)
      (code layout zeroValid mul add mulBuffers addBuffers reserve port sampler) := by
  have branches := (Interactive.Refines.dispatch layout.yes.representation layout.no.representation
    (EntryRead.output layout.hash.scheme).representation
    (accepted_refines layout zeroValid mul add mulBuffers addBuffers reserve port sampleCorrect)
    (Interactive.Refines.compute port .unit (rejected layout zeroValid))
    (width_pos layout.hash.scheme.wordFits) layout.selected.representation.fits).viewInput
      layout.selected.representation (sumView layout.yes layout.no) (fun _ => rfl)
  have combined := (Interactive.Refines.compute port .unit (HashDispatch.selector layout).program).seq branches
  convert combined using 1
  · funext value
    simp only [pure_bind]
    rfl
  · rfl

theorem source_yes (sampler : OracleComp spec layout.hash.scheme.scalar.Value) (value : layout.input.Value)
    (valid : HashDispatch.shape value.val = true) :
    source layout zeroValid mul add mulBuffers addBuffers reserve sampler value =
      EntryRead.source layout.hash.scheme zeroValid sampler
        (Hash.prepareValue layout.hash zeroValid mul add mulBuffers addBuffers reserve
          (layout.acceptedValue ⟨value.val, value.property, valid⟩)) := by
  unfold source selectedValue GuardedBranch.select
  simp only [valid, ↓reduceIte]
  rfl
theorem source_no (sampler : OracleComp spec layout.hash.scheme.scalar.Value) (value : layout.input.Value)
    (invalid : HashDispatch.shape value.val = false) :
    source layout zeroValid mul add mulBuffers addBuffers reserve sampler value = pure (rejectValue layout zeroValid value) := by
  unfold source selectedValue GuardedBranch.select
  simp only [invalid, Bool.false_eq_true, ↓reduceIte]
  rfl

end Signatures.Runtime.CaliperBackend.SchnorrAGM.ExtractionEntry
