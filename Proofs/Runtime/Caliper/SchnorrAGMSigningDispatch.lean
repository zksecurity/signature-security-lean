import Proofs.Runtime.Caliper.SchnorrAGMSigningAccept
import Proofs.Runtime.Caliper.SchnorrAGMSigningReject

/-! Signing for every represented request shape. The stored group-list length
selects two draws and signing, or deterministic rejection without draws.
Both branches produce the original scalar/group-list reply and state. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.SigningDispatch
open Caliper BoundedSource OracleComp OracleSpec
variable {w qH qS : Nat} {M F G I : Type} [Zero F] [SMul F G] [Sub G] [Neg F]
    [DecidableEq M] [DecidableEq G] {spec : OracleSpec I}
    (layout : Layouts w M F G qH qS) (zeroValid : layout.scheme.scalar.valid 0)
    (scale : Implementation .unit layout.signing.signing.arithmetic.scaleArgs layout.scheme.point (fun args => args.1 • args.2))
    (sub : Implementation .unit layout.signing.signing.arithmetic.points layout.scheme.point (fun args => args.1 - args.2))
    (negate : Implementation .unit layout.scheme.scalar layout.scheme.scalar Neg.neg)
    {slots : Nat} (scaleBuffers : scale.program.code.memBound ≤ slots)
    (subBuffers : sub.program.code.memBound ≤ slots) (negateBuffers : negate.program.code.memBound ≤ slots)
    (reserve : slots + 4 < 2 ^ w) (port : Interactive.Port w spec)

def accepted (sampler : Interactive.Code w) : Interactive.Code w :=
  .seq (.compute (accept layout).code)
    (.seq (Signing.Sampling.code layout.signing zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve port sampler)
      (.compute (wrap layout).code))
def rejected : Realizer .unit layout.no.representation layout.output.representation
    (fun value => rejectValue layout zeroValid ⟨value.val, value.property.1⟩) :=
  (reject layout zeroValid).viewInput layout.no.representation (fun value => ⟨value.val, value.property.1⟩) (fun _ => rfl)

def dispatch (sampler : Interactive.Code w) : Interactive.Code w :=
  Interactive.dispatch (accepted layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve port sampler)
    (.compute (rejected layout zeroValid).code) layout.yes.representation.encoding.words layout.no.representation.encoding.words
def code (sampler : Interactive.Code w) : Interactive.Code w :=
  .seq (.compute (selector layout).program.code) (dispatch layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve port sampler)

def selectedValue (value : layout.input.Value) : layout.selected.Value :=
  ⟨GuardedBranch.select shape value.val, (selector layout).preserves value.val value.property⟩
def source (sampler : OracleComp spec layout.scheme.scalar.Value) (value : layout.input.Value) :
    OracleComp spec layout.output.Value :=
  Sum.elim
    (fun chosen => wrapValue layout <$> Signing.Sampling.denote layout.signing zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve sampler (layout.acceptedValue chosen))
    (fun chosen => pure (rejectValue layout zeroValid ⟨chosen.val, chosen.property.1⟩))
    (sumView layout.yes layout.no (selectedValue layout value))

theorem accepted_refines {sampler : Interactive.Code w} {sampleSource : OracleComp spec layout.scheme.scalar.Value}
    (sampleCorrect : Interactive.Refines port .unit (PairSampling.input w).representation layout.scheme.scalar.representation
      (fun _ => sampleSource) sampler) :
    Interactive.Refines port .unit layout.yes.representation layout.output.representation
      (fun value => wrapValue layout <$> Signing.Sampling.denote layout.signing zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve sampleSource (layout.acceptedValue value))
      (accepted layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve port sampler) := by
  have combined := (Interactive.Refines.compute port .unit (accept layout)).seq
    ((Signing.Sampling.refines layout.signing zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve port sampleCorrect).seq
      (Interactive.Refines.compute port .unit (wrap layout)))
  convert combined using 1
  · funext value
    simp only [pure_bind, bind_pure_comp]
  · rfl

theorem refines {sampler : Interactive.Code w} {sampleSource : OracleComp spec layout.scheme.scalar.Value}
    (sampleCorrect : Interactive.Refines port .unit (PairSampling.input w).representation layout.scheme.scalar.representation
      (fun _ => sampleSource) sampler) :
    Interactive.Refines port .unit layout.input.representation layout.output.representation
      (source layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve sampleSource)
      (code layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve port sampler) := by
  have branches := (Interactive.Refines.dispatch layout.yes.representation layout.no.representation
    layout.output.representation
    (accepted_refines layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve port sampleCorrect)
    (Interactive.Refines.compute port .unit (rejected layout zeroValid))
    (width_pos layout.scheme.wordFits) layout.selected.representation.fits).viewInput
      layout.selected.representation (sumView layout.yes layout.no) (fun _ => rfl)
  have combined := (Interactive.Refines.compute port .unit (selector layout).program).seq branches
  convert combined using 1
  · funext value
    simp only [pure_bind]
    rfl
  · rfl

theorem source_yes (sampler : OracleComp spec layout.scheme.scalar.Value) (value : layout.input.Value)
    (valid : shape value.val = true) :
    source layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve sampler value =
      wrapValue layout <$> Signing.Sampling.denote layout.signing zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve sampler
        (layout.acceptedValue ⟨value.val, value.property, valid⟩) := by
  unfold source selectedValue GuardedBranch.select
  simp only [valid, ↓reduceIte]
  rfl

theorem source_no (sampler : OracleComp spec layout.scheme.scalar.Value) (value : layout.input.Value)
    (invalid : shape value.val = false) :
    source layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve sampler value = pure (rejectValue layout zeroValid value) := by
  unfold source selectedValue GuardedBranch.select
  simp only [invalid, Bool.false_eq_true, ↓reduceIte]
  rfl

end Signatures.Runtime.CaliperBackend.SchnorrAGM.SigningDispatch
