import Proofs.Runtime.Caliper.SchnorrROMTapeFreshNatural
import Proofs.Runtime.Caliper.SchnorrROMTapeRead

/-! Fresh raw replay cells from a scalar sampler and the executed dynamic
uniform adapter. Family selection, private-range subtraction and cell packet
construction are all actual Caliper code. -/

namespace Signatures.Runtime.CaliperBackend.SchnorrROMTape.Fresh
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat} {F : Type} [Zero F] (layout : Layouts w F) (zeroValid : layout.scalar.valid 0)

def scalarDenote (scalarSource : ProbComp layout.scalar.Value) (_tag : layout.counter.Value) : ProbComp layout.entry.Value :=
  Read.produced (scalarCell layout) <$> scalarSource
def privateDrawDenote (value : (pair layout).Value) : ProbComp (pair layout).Value :=
  (fun fresh => (⟨(fresh.val, value.val.2), fresh.property, value.property.2⟩ : (pair layout).Value)) <$>
    naturalSource layout ⟨value.val.1, value.property.1⟩
def privateDenote (tag : layout.counter.Value) : ProbComp layout.entry.Value :=
  privateDrawDenote layout (Read.produced (privateInput layout) tag) >>= fun value =>
    pure (Read.produced (privateCell layout zeroValid) value)
def branchDenote (scalarSource : ProbComp layout.scalar.Value) (value : (choice layout).Value) : ProbComp layout.entry.Value :=
  Sum.elim (scalarDenote layout scalarSource) (privateDenote layout zeroValid) (sumView layout.counter layout.counter value)
def denote (scalarSource : ProbComp layout.scalar.Value) (tag : layout.counter.Value) : ProbComp layout.entry.Value :=
  branchDenote layout zeroValid scalarSource (Read.produced (selector layout) tag)

def scalarCode (sampler : Interactive.Code w) : Interactive.Code w :=
  .seq (.compute (dropTag layout).implementation.program.code)
    (.seq sampler (.compute (scalarCell layout).implementation.program.code))
def privateDrawCode : Interactive.Code w :=
  Interactive.retain (naturalCode layout) (Interactive.savedBuffer (port layout) (naturalCode layout)) 1 1 1
def privateCode : Interactive.Code w :=
  .seq (.compute (privateInput layout).implementation.program.code)
    (.seq (privateDrawCode layout) (.compute (privateCell layout zeroValid).implementation.program.code))
def branchCode (sampler : Interactive.Code w) : Interactive.Code w :=
  Interactive.dispatch (scalarCode layout sampler) (privateCode layout zeroValid) 1 1
def code (sampler : Interactive.Code w) : Interactive.Code w :=
  .seq (.compute (selector layout).implementation.program.code) (branchCode layout zeroValid sampler)

omit [Zero F] in
theorem privateDraw_refines : Interactive.Refines (port layout) .unit (pair layout).representation (pair layout).representation
    (privateDrawDenote layout) (privateDrawCode layout) := by
  have retained := (natural_refines layout).retain (by decide) layout.counter.representation layout.wordFits
    (pair layout).representation.fits (pair layout).representation.fits
  have viewed := (retained.viewInput (pair layout).representation (productView layout.counter layout.counter) (fun _ => rfl)).viewOutput
    (pair layout).representation (productView layout.counter layout.counter).symm (by
      intro value
      exact congrArg (layout.counter.representation.prod layout.counter.representation (pair layout).representation.fits).encoding.encode
        ((productView layout.counter layout.counter).apply_symm_apply value))
  convert viewed using 1
  · funext value
    exact PFunctor.FreeM.comp_map (productView layout.counter layout.counter).symm
      (fun fresh => (fresh, ⟨value.val.2, value.property.2⟩)) (naturalSource layout ⟨value.val.1, value.property.1⟩)
  · rfl

theorem private_refines : Interactive.Refines (port layout) .unit layout.counter.representation layout.entry.representation
    (privateDenote layout zeroValid) (privateCode layout zeroValid) := by
  convert (Interactive.Refines.compute (port layout) .unit (privateInput layout).implementation.program).seq
    ((privateDraw_refines layout).seq
      (Interactive.Refines.compute (port layout) .unit (privateCell layout zeroValid).implementation.program)) using 1
  · funext value
    simp only [pure_bind]
    rfl
  · rfl

variable {scalarSource : ProbComp layout.scalar.Value} {sampler : Interactive.Code w}
    (scalarCorrect : Interactive.Refines (port layout) .unit layout.unit.representation layout.scalar.representation
      (fun _ => scalarSource) sampler)

omit [Zero F] in
include scalarCorrect in
theorem scalar_refines : Interactive.Refines (port layout) .unit layout.counter.representation layout.entry.representation
    (scalarDenote layout scalarSource) (scalarCode layout sampler) := by
  convert (Interactive.Refines.compute (port layout) .unit (dropTag layout).implementation.program).seq
    (scalarCorrect.seq (Interactive.Refines.compute (port layout) .unit (scalarCell layout).implementation.program)) using 1
  · funext value
    simp only [pure_bind, bind_pure_comp]
    rfl
  · rfl

include scalarCorrect in
theorem refines : Interactive.Refines (port layout) .unit layout.counter.representation layout.entry.representation
    (denote layout zeroValid scalarSource) (code layout zeroValid sampler) := by
  have dispatched := (Interactive.Refines.dispatch layout.counter.representation layout.counter.representation layout.entry.representation
    (scalar_refines layout scalarCorrect) (private_refines layout zeroValid) (width_pos layout.wordFits)
    (choice layout).representation.fits).viewInput (choice layout).representation
      (sumView layout.counter layout.counter) (fun _ => rfl)
  convert (Interactive.Refines.compute (port layout) .unit (selector layout).implementation.program).seq dispatched using 1
  · funext value
    simp only [pure_bind]
    rfl
  · rfl

end Signatures.Runtime.CaliperBackend.SchnorrROMTape.Fresh
