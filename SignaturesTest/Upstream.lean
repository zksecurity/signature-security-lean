import ArkLib.AGM.Basic
import Signatures
import Proofs
import Lean.Util.CollectAxioms

/-! Upstream representation compatibility and the seven general-attacker security endpoints. -/

#check AGM.GroupRepresentation

example {G : Type} [Group G] {p : Nat} [Fact (Nat.Prime p)] [PrimeOrderWith G p]
    {ι : Type} [Fintype ι] {basis : ι → G} {target : G}
    (repr : AGM.GroupRepresentation (p := p) basis target) :
    (∏ i, basis i ^ (repr.exponents i).val) = target :=
  repr.hEq

example {G : Type} [Group G] {p : Nat} [Fact (Nat.Prime p)] [PrimeOrderWith G p]
    {ι : Type} [Fintype ι] {basis : ι → G} {target : G}
    (repr : AGM.GroupRepresentation (p := p) basis target) : 0 < p :=
  repr.modulus_pos

open Lean Meta in
run_meta do
  let expected := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``BLS.cocdh_security, ``BLS.agm_security, ``OOPS.agm_security,
      ``Proximity.agm_security, ``Schnorr.rom_security, ``Schnorr.agm_security,
      ``Schnorr.NonzeroNonce.rom_security] do
    let axioms ← collectAxioms name
    unless axioms.size == expected.size && axioms.all expected.contains do
      throwError "{name}: unexpected public theorem axiom footprint {axioms}"
