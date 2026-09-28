import ArkLib.AGM.Basic
import Signatures

/-! Upstream representation compatibility and the four supported security endpoints. -/

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

/-- info: 'BLS.Statement.bls_eufcma_of_cocdh_machine_hardness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BLS.Statement.bls_eufcma_of_cocdh_machine_hardness

/-- info: 'BLS.Statement.bls_lazy_agm_of_dlog_machine_hardness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BLS.Statement.bls_lazy_agm_of_dlog_machine_hardness

/-- info: 'OOPS.Statement.oops_lazy_agm_of_dlog_machine_hardness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms OOPS.Statement.oops_lazy_agm_of_dlog_machine_hardness

/-- info: 'Proximity.Statement.proximity_lazy_agm_of_dlog_machine_hardness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Proximity.Statement.proximity_lazy_agm_of_dlog_machine_hardness
