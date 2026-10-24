import Proofs.Runtime.Caliper.SchnorrROMTapeCallerPrepare
import Proofs.Runtime.Caliper.SchnorrROMTapeQuery

/-! Caller requests, replay and reply decoding as one executed program. The
private range is copied across the query and decoded by actual word operations.
Only the local scalar sampler has an implementation premise. -/

namespace Signatures.Runtime.CaliperBackend.SchnorrROMTape.Caller
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat} {F : Type} [Zero F] (layout : Layouts w F) (zeroValid : layout.scalar.valid 0)

def retainedDenote (scalarSource : ProbComp layout.scalar.Value) (value : (retainedInput layout).Value) :
    ProbComp (retainedOutput layout).Value :=
  (fun answer => (⟨(answer.val, value.val.2), answer.property, value.property.2⟩ : (retainedOutput layout).Value)) <$>
    Query.denote layout zeroValid scalarSource ⟨value.val.1, value.property.1⟩
def privateDenote (scalarSource : ProbComp layout.scalar.Value) (value : (privateInput layout).Value) :
    ProbComp (Reply.privateOutput layout).Value :=
  retainedDenote layout zeroValid scalarSource (Read.produced (prepare layout zeroValid) value) >>=
    fun answer => pure (Read.produced (finish layout) answer)
def scalarDenote (scalarSource : ProbComp layout.scalar.Value) (value : (Read.store layout).Value) :
    ProbComp (Reply.scalarOutput layout).Value :=
  Query.denote layout zeroValid scalarSource (Read.produced (scalarPacket layout zeroValid) value) >>=
    fun answer => pure (Read.produced (Reply.scalarDecoder layout) answer)

def retainedCode (sampler : Interactive.Code w) : Interactive.Code w :=
  Interactive.retain (Query.code layout zeroValid sampler)
    (Interactive.savedBuffer (Fresh.port layout) (Query.code layout zeroValid sampler))
    (Read.input layout).representation.encoding.words (Read.output layout).representation.encoding.words
    (Reply.range layout).representation.encoding.words
def privateCode (sampler : Interactive.Code w) : Interactive.Code w :=
  .seq (.compute (prepare layout zeroValid).implementation.program.code)
    (.seq (retainedCode layout zeroValid sampler) (.compute (finish layout).implementation.program.code))
def scalarCode (sampler : Interactive.Code w) : Interactive.Code w :=
  .seq (.compute (scalarPacket layout zeroValid).implementation.program.code)
    (.seq (Query.code layout zeroValid sampler) (.compute (Reply.scalarDecoder layout).implementation.program.code))

variable {scalarSource : ProbComp layout.scalar.Value} {sampler : Interactive.Code w}
    (scalarCorrect : Interactive.Refines (Fresh.port layout) .unit layout.unit.representation layout.scalar.representation
      (fun _ => scalarSource) sampler)

include scalarCorrect in
theorem retained_refines : Interactive.Refines (Fresh.port layout) .unit
    (retainedInput layout).representation (retainedOutput layout).representation
    (retainedDenote layout zeroValid scalarSource) (retainedCode layout zeroValid sampler) := by
  have retained := (Query.refines layout zeroValid scalarCorrect).retain (by decide) (Reply.range layout).representation
    layout.wordFits (retainedInput layout).representation.fits (retainedOutput layout).representation.fits
  have viewed := (retained.viewInput (retainedInput layout).representation
    (productView (Read.input layout) (Reply.range layout)) (fun _ => rfl)).viewOutput
      (retainedOutput layout).representation (productView (Read.output layout) (Reply.range layout)).symm (by
        intro value
        exact congrArg ((Read.output layout).representation.prod (Reply.range layout).representation
          (retainedOutput layout).representation.fits).encoding.encode
            ((productView (Read.output layout) (Reply.range layout)).apply_symm_apply value))
  convert viewed using 1
  · funext value
    exact PFunctor.FreeM.comp_map (productView (Read.output layout) (Reply.range layout)).symm
      (fun answer => (answer, ⟨value.val.2, value.property.2⟩))
      (Query.denote layout zeroValid scalarSource ⟨value.val.1, value.property.1⟩)
  · rfl

include scalarCorrect in
theorem private_refines : Interactive.Refines (Fresh.port layout) .unit
    (privateInput layout).representation (Reply.privateOutput layout).representation
    (privateDenote layout zeroValid scalarSource) (privateCode layout zeroValid sampler) := by
  convert (Interactive.Refines.compute (Fresh.port layout) .unit (prepare layout zeroValid).implementation.program).seq
    ((retained_refines layout zeroValid scalarCorrect).seq
      (Interactive.Refines.compute (Fresh.port layout) .unit (finish layout).implementation.program)) using 1
  · funext value
    simp only [pure_bind]
    rfl
  · rfl

include scalarCorrect in
theorem scalar_refines : Interactive.Refines (Fresh.port layout) .unit
    (Read.store layout).representation (Reply.scalarOutput layout).representation
    (scalarDenote layout zeroValid scalarSource) (scalarCode layout zeroValid sampler) := by
  convert (Interactive.Refines.compute (Fresh.port layout) .unit (scalarPacket layout zeroValid).implementation.program).seq
    ((Query.refines layout zeroValid scalarCorrect).seq
      (Interactive.Refines.compute (Fresh.port layout) .unit (Reply.scalarDecoder layout).implementation.program)) using 1
  · funext value
    simp only [pure_bind]
    rfl
  · rfl

end Signatures.Runtime.CaliperBackend.SchnorrROMTape.Caller
