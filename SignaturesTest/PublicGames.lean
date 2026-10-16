import Signatures.BLS.Statement
import Signatures.OOPS.Statement
import Signatures.Proximity.Statement
import Signatures.Schnorr.Statement
import Lean.Util.CollectAxioms

/-! The mathematical games are independent of machine contracts. The existing
public security statements use those exact games, preserving source-game proofs
and their axiom guards. This is an API separation, not a change of experiment. -/

open Lean Meta

namespace SignaturesTest.PublicGames

run_meta do
  let games := #[
    (``BLS.Game.agm, `Signatures.BLS.Game), (``BLS.Game.rom, `Signatures.BLS.Game),
    (``OOPS.Game.agm, `Signatures.OOPS.Game),
    (``Proximity.Game.agm, `Signatures.Proximity.Game),
    (``Proximity.Game.collision, `Signatures.Proximity.Game),
    (``Schnorr.Game.agm, `Signatures.Schnorr.Game),
    (``Schnorr.Game.rom, `Signatures.Schnorr.Game),
    (``Schnorr.Game.nonzeroRom, `Signatures.Schnorr.Game)]
  for (name, moduleName) in games do
    unless (← findModuleOf? name) == some moduleName do
      throwError "{name}: keep the mathematical game separate from execution contracts"
    let type := (← getConstInfo name).type
    if (type.find? fun e => match e with
        | .const n _ => n.toString.startsWith "Signatures.Runtime." ||
            n.toString.endsWith "SecurityModel" || n.toString.contains ".General"
        | _ => false).isSome then
      throwError "{name}: a mathematical game must not require a machine or resource certificate"
    for axiomName in (← collectAxioms name) do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"

example (curve : Model.PairingCurve) [BLS.AGMSecurityModel curve]
    (n : Nat) (q : BLS.QueryAllowance) (A : BLS.AlgebraicAdversary curve n q) :
    BLS.agmEufCmaGame curve n A = BLS.Game.agm curve n A.source := rfl

example (curve : Model.PairingCurve) [BLS.CoCDHSecurityModel curve]
    (n : Nat) (q : BLS.QueryAllowance) (A : BLS.UnrestrictedAdversary curve n q) :
    BLS.cocdhEufCmaGame curve n A = BLS.Game.rom curve n A.source := rfl

example (curve : Model.PairingCurve) [OOPS.AGMSecurityModel curve]
    (n degree : Nat) (q : OOPS.QueryAllowance) (A : OOPS.AlgebraicAdversary curve n degree q) :
    OOPS.agmEufCmaGame curve n degree A = OOPS.Game.agm curve n degree A.source := rfl

example (curve : Model.PairingCurve) [Proximity.AGMSecurityModel curve]
    (n dimension : Nat) (q : Proximity.QueryAllowance)
    (A : Proximity.AlgebraicAdversary curve n dimension q) :
    Proximity.agmEufCmaGame curve n dimension A = Proximity.Game.agm curve n dimension A.source := rfl

example (curve : Model.PairingCurve) [Proximity.AGMSecurityModel curve]
    (n dimension : Nat) (q : Proximity.QueryAllowance)
    (A : Proximity.AlgebraicAdversary curve n dimension q) :
    Proximity.freshCollisionGame curve n dimension A = Proximity.Game.collision curve n dimension A.source := rfl

example (curve : Model.CyclicCurve) [Schnorr.AGMSecurityModel curve]
    (n : Nat) (q : Schnorr.QueryAllowance) (A : Schnorr.AlgebraicAdversary curve n q) :
    Schnorr.agmEufCmaGame curve n A = Schnorr.Game.agm curve n A.source := rfl

example (curve : Model.CyclicCurve) [Schnorr.ROMSecurityModel curve]
    (n : Nat) (q : Schnorr.QueryAllowance) (A : Schnorr.UnrestrictedAdversary curve n q) :
    Schnorr.romEufCmaGame curve n A = Schnorr.Game.rom curve n A.source.main := rfl

example (curve : Model.CyclicCurve) [Schnorr.NonzeroNonce.ROMSecurityModel curve]
    (n : Nat) (q : Schnorr.QueryAllowance) (A : Schnorr.NonzeroNonce.UnrestrictedAdversary curve n q) :
    Schnorr.NonzeroNonce.romEufCmaGame curve n A = Schnorr.Game.nonzeroRom curve n A.source.main := rfl

end SignaturesTest.PublicGames
