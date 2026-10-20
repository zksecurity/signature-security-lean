import Signatures.Runtime.Caliper.SchnorrROMEnumeratedDraw
import Signatures.Runtime.Caliper.SchnorrROMTapeCallerMemory
import Signatures.Runtime.Caliper.SchnorrROMTapeCallerSource

/-! Complete raw replay queries with the constructed finite-index scalar draw.
There is no local sampler implementation premise. The source is the established
raw oracle interpreted by `LazyROM.sample`, including both returned tapes.
The same programs have stored-code, time and every-visited-state memory bounds. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROMTape.EnumeratedReplay
open Caliper BoundedSource OracleComp OracleSpec PrivateSampler.Enumerated
variable {w : Nat} {F : Type} [Zero F] (params : Parameters w F)

def privateCode : Interactive.Code w := Caller.privateCode (tape params) trivial (Direct.code params)
def scalarCode : Interactive.Code w := Caller.scalarCode (tape params) trivial (Direct.code params)

omit [Zero F] in
theorem sample_eq :
    letI := sampleable params
    Fresh.sample (tape params) (Direct.source params) = _root_.Schnorr.LazyROM.sample := by
  let := sampleable params
  funext query
  rcases query with n | ⟨⟩
  · rfl
  · exact Direct.uniform params

theorem private_source (n : Nat) (state : Schnorr.RawTape.State F)
    (valid : (Caller.privateInput (tape params)).valid (Caller.rawPrivate n state)) :
    letI := sampleable params
    Subtype.val <$> Caller.privateDenote (tape params) trivial (Direct.source params) ⟨Caller.rawPrivate n state, valid⟩ =
      Caller.privateResult n <$> simulateQ _root_.Schnorr.LazyROM.sample ((Schnorr.RawTape.oracle (.inl n)).run state) := by
  rw [← sample_eq params]
  exact Caller.private_source (tape params) trivial (Direct.source params) n state valid

theorem scalar_source (state : Schnorr.RawTape.State F)
    (valid : (Read.store (tape params)).valid (Caller.rawScalar state)) :
    letI := sampleable params
    Subtype.val <$> Caller.scalarDenote (tape params) trivial (Direct.source params) ⟨Caller.rawScalar state, valid⟩ =
      Caller.scalarResult <$> simulateQ _root_.Schnorr.LazyROM.sample ((Schnorr.RawTape.oracle (.inr ())).run state) := by
  rw [← sample_eq params]
  exact Caller.scalar_source (tape params) trivial (Direct.source params) state valid

theorem private_observe (n : Nat) (state : Schnorr.RawTape.State F)
    (valid : (Caller.privateInput (tape params)).valid (Caller.rawPrivate n state))
    (random : RandomTape w) (before : State w)
    (holds : (Caller.privateInput (tape params)).representation.Holds ⟨Caller.rawPrivate n state, valid⟩ before) :
    letI := sampleable params
    (fun result => (Interactive.observe (Reply.privateOutput (tape params)).representation result).map Subtype.val) <$>
        (privateCode params).execute (Fresh.port (tape params)) .unit random before =
      some <$> (Caller.privateResult n <$>
        simulateQ _root_.Schnorr.LazyROM.sample ((Schnorr.RawTape.oracle (.inl n)).run state)) := by
  rw [← sample_eq params]
  exact Caller.private_observe (tape params) trivial (Direct.refines params) n state valid random before holds

theorem scalar_observe (state : Schnorr.RawTape.State F)
    (valid : (Read.store (tape params)).valid (Caller.rawScalar state))
    (random : RandomTape w) (before : State w)
    (holds : (Read.store (tape params)).representation.Holds ⟨Caller.rawScalar state, valid⟩ before) :
    letI := sampleable params
    (fun result => (Interactive.observe (Reply.scalarOutput (tape params)).representation result).map Subtype.val) <$>
        (scalarCode params).execute (Fresh.port (tape params)) .unit random before =
      some <$> (Caller.scalarResult <$>
        simulateQ _root_.Schnorr.LazyROM.sample ((Schnorr.RawTape.oracle (.inr ())).run state)) := by
  rw [← sample_eq params]
  exact Caller.scalar_observe (tape params) trivial (Direct.refines params) state valid random before holds

theorem private_descriptionFits : ((privateCode params).lower (Fresh.port (tape params))).DescriptionFits :=
  Caller.private_descriptionFits (tape params) trivial (Direct.code params) (Direct.descriptionFits params)
    (by have := Direct.buffers params; have := params.wordFits; omega)

theorem scalar_descriptionFits : ((scalarCode params).lower (Fresh.port (tape params))).DescriptionFits :=
  Caller.scalar_descriptionFits (tape params) trivial (Direct.code params) (Direct.descriptionFits params)
    (by have := Direct.buffers params; have := params.wordFits; omega)

/-- Complete resources for the original private query, with its dynamic range. -/
theorem private_within :
    letI := sampleable params
    Interactive.Within (Fresh.port (tape params)) (Caller.privateInput (tape params)) (Reply.privateOutput (tape params))
      (Caller.privateWords (tape params) trivial 125)
      (5 * Caller.privateWords (tape params) trivial 125 + 4 * Caller.nameSlots (tape params) trivial 125 3 + 3 +
        (Caller.privateInput (tape params)).representation.encoding.words + Caller.privateTime (tape params) trivial 26)
      (Caller.privateTime (tape params) trivial 26)
      (fun value => Caller.privateResult value.val.1 <$>
        simulateQ _root_.Schnorr.LazyROM.sample
          ((Schnorr.RawTape.oracle (.inl value.val.1)).run ⟨value.val.2.1, value.val.2.2⟩)) := by
  let := sampleable params
  have bounded := Interactive.within_of_refines_accounted
    (Caller.private_refines (tape params) trivial (Direct.refines params))
    (Caller.private_time (tape params) trivial (Direct.refines params) (Direct.time_bound params))
    (Caller.private_words (tape params) trivial (Direct.code params) (Direct.code_words params))
    (Caller.private_names (tape params) trivial (Direct.code params) (Direct.code_words params) (Direct.names params))
    (private_descriptionFits params)
  exact bounded.congr (fun value => private_source params value.val.1 ⟨value.val.2.1, value.val.2.2⟩ value.property)

/-- Complete resources for a public scalar query. Only one scalar-family cell
is appended on a miss; the direct draw does not create a private replay cell. -/
theorem scalar_within :
    letI := sampleable params
    Interactive.Within (Fresh.port (tape params)) (Read.store (tape params)) (Reply.scalarOutput (tape params))
      (Caller.scalarWords (tape params) trivial 125)
      (5 * Caller.scalarWords (tape params) trivial 125 + 4 * Caller.nameSlots (tape params) trivial 125 3 + 3 +
        (Read.store (tape params)).representation.encoding.words + Caller.scalarTime (tape params) trivial 26)
      (Caller.scalarTime (tape params) trivial 26)
      (fun value => Caller.scalarResult <$>
        simulateQ _root_.Schnorr.LazyROM.sample
          ((Schnorr.RawTape.oracle (.inr ())).run ⟨value.val.1, value.val.2⟩)) := by
  let := sampleable params
  have bounded := Interactive.within_of_refines_accounted
    (Caller.scalar_refines (tape params) trivial (Direct.refines params))
    (Caller.scalar_time (tape params) trivial (Direct.refines params) (Direct.time_bound params))
    (Caller.scalar_words (tape params) trivial (Direct.code params) (Direct.code_words params))
    (Caller.scalar_names (tape params) trivial (Direct.code params) (Direct.code_words params) (Direct.names params))
    (scalar_descriptionFits params)
  exact bounded.congr (fun value => scalar_source params ⟨value.val.1, value.val.2⟩ value.property)

end Signatures.Runtime.CaliperBackend.SchnorrROMTape.EnumeratedReplay
