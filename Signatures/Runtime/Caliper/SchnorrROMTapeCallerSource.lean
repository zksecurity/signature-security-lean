import Signatures.Runtime.Caliper.SchnorrROMTapeCaller

/-! The complete caller programs implement the original raw replay queries.
Their observed output is already decoded by executed instructions and includes
both tapes; private replies also echo their retained request range. -/

namespace Signatures.Runtime.CaliperBackend.SchnorrROMTape.Caller
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat} {F : Type} [Zero F] (layout : Layouts w F) (zeroValid : layout.scalar.valid 0)
    (scalarSource : ProbComp layout.scalar.Value)

def privateResult (n : Nat) (value : Fin (n + 1) × Schnorr.RawTape.State F) :=
  (n, value.1.val, value.2.saved, value.2.remaining)
def scalarResult (value : F × Schnorr.RawTape.State F) :=
  (value.1, value.2.saved, value.2.remaining)

theorem private_source (n : Nat) (state : Schnorr.RawTape.State F)
    (valid : (privateInput layout).valid (rawPrivate n state)) :
    Subtype.val <$> privateDenote layout zeroValid scalarSource ⟨rawPrivate n state, valid⟩ =
      privateResult n <$> simulateQ (Fresh.sample layout scalarSource) ((Schnorr.RawTape.oracle (.inl n)).run state) := by
  have admitted := (privatePacket layout zeroValid).implementation.preserves (rawPrivate n state) valid
  change (Read.input layout).valid (Read.rawInput (.inl n) state) at admitted
  have original := Fresh.read_rawOracle layout zeroValid scalarSource (.inl n) state admitted
  have mapped := congrArg (Functor.map (privateResult n)) original
  simpa only [privateDenote, retainedDenote, bind_pure_comp, Functor.map_map,
    Read.produced, Query.denote, privateResult, rawPrivate, Read.rawOutput, Reply.privateSource,
    Read.rawInput, Schnorr.RawTape.tag, Schnorr.RawTape.family, Schnorr.SeedTape.familyTag,
    Schnorr.RawTape.decode, Schnorr.decodeReply, Prod.mk.eta] using mapped

theorem scalar_source (state : Schnorr.RawTape.State F)
    (valid : (Read.store layout).valid (rawScalar state)) :
    Subtype.val <$> scalarDenote layout zeroValid scalarSource ⟨rawScalar state, valid⟩ =
      scalarResult <$> simulateQ (Fresh.sample layout scalarSource) ((Schnorr.RawTape.oracle (.inr ())).run state) := by
  have admitted := (scalarPacket layout zeroValid).implementation.preserves (rawScalar state) valid
  change (Read.input layout).valid (Read.rawInput (.inr ()) state) at admitted
  have original := Fresh.read_rawOracle layout zeroValid scalarSource (.inr ()) state admitted
  have mapped := congrArg (Functor.map (scalarResult (F := F))) original
  simpa only [scalarDenote, bind_pure_comp, Functor.map_map,
    Read.produced, Query.denote, scalarResult, rawScalar, Read.rawOutput, Reply.scalarSource,
    Read.rawInput, Schnorr.RawTape.tag, Schnorr.RawTape.family, Schnorr.SeedTape.familyTag,
    Schnorr.RawTape.decode, Schnorr.decodeReply, Prod.mk.eta] using mapped

variable {scalarSource} {sampler : Interactive.Code w}
    (scalarCorrect : Interactive.Refines (Fresh.port layout) .unit layout.unit.representation layout.scalar.representation
      (fun _ => scalarSource) sampler)

include scalarCorrect in
theorem private_observe (n : Nat) (state : Schnorr.RawTape.State F)
    (valid : (privateInput layout).valid (rawPrivate n state)) (tape : RandomTape w) (before : State w)
    (holds : (privateInput layout).representation.Holds ⟨rawPrivate n state, valid⟩ before) :
    (fun result => (Interactive.observe (Reply.privateOutput layout).representation result).map Subtype.val) <$>
        (privateCode layout zeroValid sampler).execute (Fresh.port layout) .unit tape before =
      some <$> (privateResult n <$>
        simulateQ (Fresh.sample layout scalarSource) ((Schnorr.RawTape.oracle (.inl n)).run state)) := by
  have observed := (private_refines layout zeroValid scalarCorrect).observe tape ⟨rawPrivate n state, valid⟩ before holds
  have mapped := congrArg (Functor.map (Option.map Subtype.val)) observed
  calc
    _ = some <$> (Subtype.val <$> privateDenote layout zeroValid scalarSource ⟨rawPrivate n state, valid⟩) := by
      simpa only [Functor.map_map, Option.map_some] using mapped
    _ = _ := congrArg (Functor.map some) (private_source layout zeroValid scalarSource n state valid)

include scalarCorrect in
theorem scalar_observe (state : Schnorr.RawTape.State F)
    (valid : (Read.store layout).valid (rawScalar state)) (tape : RandomTape w) (before : State w)
    (holds : (Read.store layout).representation.Holds ⟨rawScalar state, valid⟩ before) :
    (fun result => (Interactive.observe (Reply.scalarOutput layout).representation result).map Subtype.val) <$>
        (scalarCode layout zeroValid sampler).execute (Fresh.port layout) .unit tape before =
      some <$> (scalarResult <$>
        simulateQ (Fresh.sample layout scalarSource) ((Schnorr.RawTape.oracle (.inr ())).run state)) := by
  have observed := (scalar_refines layout zeroValid scalarCorrect).observe tape ⟨rawScalar state, valid⟩ before holds
  have mapped := congrArg (Functor.map (Option.map Subtype.val)) observed
  calc
    _ = some <$> (Subtype.val <$> scalarDenote layout zeroValid scalarSource ⟨rawScalar state, valid⟩) := by
      simpa only [Functor.map_map, Option.map_some] using mapped
    _ = _ := congrArg (Functor.map some) (scalar_source layout zeroValid scalarSource state valid)

end Signatures.Runtime.CaliperBackend.SchnorrROMTape.Caller
