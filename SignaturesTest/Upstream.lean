import Signatures
import Proofs
import Lean.Util.CollectAxioms

/-! The seven general-attacker security endpoints and their axiom footprint. -/

open Lean Meta in
run_meta do
  let expected := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``BLS.cocdh_security, ``BLS.agm_security, ``OOPS.agm_security,
      ``Proximity.agm_security, ``Schnorr.rom_security, ``Schnorr.agm_security,
      ``Schnorr.NonzeroNonce.rom_security] do
    let axioms ← collectAxioms name
    unless axioms.size == expected.size && axioms.all expected.contains do
      throwError "{name}: unexpected public theorem axiom footprint {axioms}"
