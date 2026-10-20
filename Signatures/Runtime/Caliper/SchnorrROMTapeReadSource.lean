import Signatures.Runtime.Caliper.SchnorrROMTapeRead

/-! Exact connection to the original raw oracle, preserving all private query
families. The only source premise describes the local fresh-cell draw. -/

namespace Signatures.Runtime.CaliperBackend.SchnorrROMTape.Read
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat} {F I : Type} [Zero F] {spec : OracleSpec.{0, 0} I} (layout : Layouts w F)

def rawInput (i : (Schnorr.RawTape.Spec F).Domain) (state : Schnorr.RawTape.State F) : Input F :=
  (Schnorr.RawTape.tag i, (0, 0, 0), state.saved, state.remaining)

def rawOutput (i : (Schnorr.RawTape.Spec F).Domain) (value : Output F) :
    (Schnorr.RawTape.Spec F).Range i × Schnorr.RawTape.State F :=
  (Schnorr.RawTape.decode i value.1, ⟨value.2.1, value.2.2⟩)

theorem decode_encode (i : (Schnorr.RawTape.Spec F).Domain) (answer : (Schnorr.RawTape.Spec F).Range i) :
    Schnorr.RawTape.decode i (Schnorr.RawTape.encode i answer) = answer := by
  rcases i with n | ⟨⟩ <;> simp [Schnorr.RawTape.decode, Schnorr.RawTape.encode, Schnorr.decode_encode]

/-- A hit removes the first matching reply; a miss records one fresh reply.
The equality includes the complete saved and remaining tapes. -/
theorem rawOracle
    (drawSource : layout.counter.Value → OracleComp spec layout.entry.Value)
    (sample : QueryImpl (Schnorr.RawTape.Spec F) (OracleComp spec))
    (i : (Schnorr.RawTape.Spec F).Domain) (state : Schnorr.RawTape.State F)
    (valid : (input layout).valid (rawInput i state))
    (drawEqual : Subtype.val <$> drawSource ⟨Schnorr.RawTape.tag i, valid.1⟩ =
      Schnorr.RawTape.encode i <$> sample i) :
    (fun value => rawOutput i value.val) <$> denote layout drawSource ⟨rawInput i state, valid⟩ =
      simulateQ sample ((Schnorr.RawTape.oracle i).run state) := by
  have observed := congrArg (Functor.map (rawOutput i))
    (denote_value layout drawSource ⟨rawInput i state, valid⟩)
  simp only [Functor.map_map] at observed
  rw [observed]
  cases found : (Schnorr.SeedTape.pop (Schnorr.RawTape.tag i) (0, (0 : F), 0) state.remaining).1 with
  | false =>
      have rest := Schnorr.SeedTape.pop_miss_rest (Schnorr.RawTape.tag i) (0, (0 : F), 0) state.remaining found
      have sampled := congrArg
        (Functor.map (fun cell => rawOutput i (cell, state.saved ++ [cell], state.remaining))) drawEqual
      simpa [rawInput, Schnorr.RawTape.oracle, StateT.run, found, rawOutput, rest, Functor.map_map, decode_encode] using sampled
  | true =>
      simp [rawInput, Schnorr.RawTape.oracle, StateT.run, found, rawOutput]

/-- Observation of the actual word program agrees with the source oracle.
Decoding here is a specification of the output bytes. -/
theorem observe_rawOracle
    (port : Interactive.Port w spec) (draw : Interactive.Code w)
    (drawSource : layout.counter.Value → OracleComp spec layout.entry.Value)
    (drawCorrect : Interactive.Refines port .unit layout.counter.representation layout.entry.representation drawSource draw)
    (sample : QueryImpl (Schnorr.RawTape.Spec F) (OracleComp spec))
    (i : (Schnorr.RawTape.Spec F).Domain) (state : Schnorr.RawTape.State F)
    (valid : (input layout).valid (rawInput i state))
    (drawEqual : Subtype.val <$> drawSource ⟨Schnorr.RawTape.tag i, valid.1⟩ =
      Schnorr.RawTape.encode i <$> sample i)
    (tape : RandomTape w) (before : Caliper.State w)
    (holds : (input layout).representation.Holds ⟨rawInput i state, valid⟩ before) :
    (fun result => (Interactive.observe (output layout).representation result).map (fun value => rawOutput i value.val)) <$>
        (code layout port draw).execute port .unit tape before =
      some <$> simulateQ sample ((Schnorr.RawTape.oracle i).run state) := by
  have observed := (refines drawCorrect).observe tape ⟨rawInput i state, valid⟩ before holds
  have mapped := congrArg (Functor.map (Option.map (fun value => rawOutput i value.val))) observed
  calc
    _ = some <$> ((fun value => rawOutput i value.val) <$> denote layout drawSource ⟨rawInput i state, valid⟩) := by
      simpa only [Functor.map_map, Option.map_some] using mapped
    _ = _ := congrArg (Functor.map some) (rawOracle layout drawSource sample i state valid drawEqual)

end Signatures.Runtime.CaliperBackend.SchnorrROMTape.Read
