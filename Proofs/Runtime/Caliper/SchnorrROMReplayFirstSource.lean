import Proofs.Runtime.Caliper.SchnorrROMReplayFirstBounds

/-! The retained first-pass selector agrees with the original optional
fork-point observation; its complete terminal result remains available. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.ReplayFirst
open Caliper BoundedSource SchnorrROMTape OracleComp OracleSpec
variable {w : Nat} {M F G A : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G]
    [DecidableEq M] [DecidableEq G] (config : Signing.Enumerated.Configuration w M F G)
    (caller : Pass.Caller config A) (ops : Handler.Operations config) (qH : Nat) (indexFits : qH + 1 < 2 ^ w)

theorem source_selector_original (cost : PrimitiveCosts) (fuel : Nat)
    (value : {value : Pass.Initialization.Input config // Pass.Replay.ready config fuel value}) :
    (fun answer => Schnorr.asIndex qH answer.1.val) <$> source config caller ops qH indexFits fuel value =
      (fun first => (Terminal.observed config first).1.bind (fun returned =>
        Schnorr.selectPass (G₂ := G) (K := M) cost qH (returned, first.2.val.1))) <$>
          Pass.source config caller ops fuel value.val := by
  unfold ReplayFirst.source
  rw [Functor.map_map]
  apply congrArg (fun observe => observe <$> Pass.source config caller ops fuel value.val)
  funext first
  exact PassSelection.source_original config cost qH first

end Signatures.Runtime.CaliperBackend.SchnorrROM.ReplayFirst
