import Proofs.Runtime.Caliper.SchnorrAGMHashAccept
import Proofs.Runtime.Caliper.SchnorrAGMHashReject

/-! Hashing for every represented request shape. The stored length test selects
the actual hash core or deterministic rejection; malformed requests cannot
invoke the challenge sampler. Each branch retains the original source state. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.HashDispatch
open Caliper BoundedSource OracleComp OracleSpec
variable {w qH qS : Nat} {M F G I : Type} [Zero F] [Mul F] [Add F] [DecidableEq F] [DecidableEq M] [DecidableEq G]
    {spec : OracleSpec I} (layout : Layouts w M F G qH qS) (zeroValid : layout.hash.scheme.scalar.valid 0)
    (mul : Implementation .unit layout.hash.scheme.affine layout.hash.scheme.scalar (fun value => value.1 * value.2))
    (add : Implementation .unit layout.hash.scheme.affine layout.hash.scheme.scalar (fun value => value.1 + value.2))
    {slots : Nat} (mulBuffers : mul.program.code.memBound ≤ slots) (addBuffers : add.program.code.memBound ≤ slots)
    (reserve : slots + 4 < 2 ^ w) (port : Interactive.Port w spec)

def accepted (sampler : Interactive.Code w) : Interactive.Code w :=
  .seq (.compute (accept layout).code) (Hash.code layout.hash zeroValid mul add mulBuffers addBuffers reserve port sampler)
def rejected : Realizer .unit layout.no.representation (Read.output layout.hash.scheme).representation
    (fun value => rejectValue layout zeroValid ⟨value.val, value.property.1⟩) :=
  (reject layout zeroValid).viewInput layout.no.representation (fun value => ⟨value.val, value.property.1⟩) (fun _ => rfl)

def dispatch (sampler : Interactive.Code w) : Interactive.Code w :=
  Interactive.dispatch (accepted layout zeroValid mul add mulBuffers addBuffers reserve port sampler)
    (.compute (rejected layout zeroValid).code) layout.yes.representation.encoding.words layout.no.representation.encoding.words
def code (sampler : Interactive.Code w) : Interactive.Code w :=
  .seq (.compute (selector layout).program.code) (dispatch layout zeroValid mul add mulBuffers addBuffers reserve port sampler)

def selectedValue (value : layout.input.Value) : layout.selected.Value :=
  ⟨GuardedBranch.select shape value.val, (selector layout).preserves value.val value.property⟩
def source (sampler : OracleComp spec layout.hash.scheme.scalar.Value) (value : layout.input.Value) :
    OracleComp spec (Read.output layout.hash.scheme).Value :=
  Sum.elim
    (fun chosen => Hash.source layout.hash zeroValid mul add mulBuffers addBuffers reserve sampler (layout.acceptedValue chosen))
    (fun chosen => pure (rejectValue layout zeroValid ⟨chosen.val, chosen.property.1⟩))
    (sumView layout.yes layout.no (selectedValue layout value))

theorem accepted_refines {sampler : Interactive.Code w} {sampleSource : OracleComp spec layout.hash.scheme.scalar.Value}
    (sampleCorrect : Interactive.Refines port .unit (PairSampling.input w).representation layout.hash.scheme.scalar.representation
      (fun _ => sampleSource) sampler) :
    Interactive.Refines port .unit layout.yes.representation (Read.output layout.hash.scheme).representation
      (fun value => Hash.source layout.hash zeroValid mul add mulBuffers addBuffers reserve sampleSource (layout.acceptedValue value))
      (accepted layout zeroValid mul add mulBuffers addBuffers reserve port sampler) := by
  have combined := (Interactive.Refines.compute port .unit (accept layout)).seq
    (Hash.refines layout.hash zeroValid mul add mulBuffers addBuffers reserve port sampleCorrect)
  convert combined using 1
  · funext value
    simp only [pure_bind]
  · rfl

theorem refines {sampler : Interactive.Code w} {sampleSource : OracleComp spec layout.hash.scheme.scalar.Value}
    (sampleCorrect : Interactive.Refines port .unit (PairSampling.input w).representation layout.hash.scheme.scalar.representation
      (fun _ => sampleSource) sampler) :
    Interactive.Refines port .unit layout.input.representation (Read.output layout.hash.scheme).representation
      (source layout zeroValid mul add mulBuffers addBuffers reserve sampleSource)
      (code layout zeroValid mul add mulBuffers addBuffers reserve port sampler) := by
  have branches := (Interactive.Refines.dispatch layout.yes.representation layout.no.representation
    (Read.output layout.hash.scheme).representation
    (accepted_refines layout zeroValid mul add mulBuffers addBuffers reserve port sampleCorrect)
    (Interactive.Refines.compute port .unit (rejected layout zeroValid))
    (width_pos layout.hash.scheme.wordFits) layout.selected.representation.fits).viewInput
      layout.selected.representation (sumView layout.yes layout.no) (fun _ => rfl)
  have combined := (Interactive.Refines.compute port .unit (selector layout).program).seq branches
  convert combined using 1
  · funext value
    simp only [pure_bind]
    rfl
  · rfl

theorem source_yes (sampler : OracleComp spec layout.hash.scheme.scalar.Value) (value : layout.input.Value)
    (valid : shape value.val = true) :
    source layout zeroValid mul add mulBuffers addBuffers reserve sampler value =
      Hash.source layout.hash zeroValid mul add mulBuffers addBuffers reserve sampler
        (layout.acceptedValue ⟨value.val, value.property, valid⟩) := by
  unfold source selectedValue GuardedBranch.select
  simp only [valid, ↓reduceIte]
  rfl

theorem source_no (sampler : OracleComp spec layout.hash.scheme.scalar.Value) (value : layout.input.Value)
    (invalid : shape value.val = false) :
    source layout zeroValid mul add mulBuffers addBuffers reserve sampler value = pure (rejectValue layout zeroValid value) := by
  unfold source selectedValue GuardedBranch.select
  simp only [invalid, Bool.false_eq_true, ↓reduceIte]
  rfl

end Signatures.Runtime.CaliperBackend.SchnorrAGM.HashDispatch
