import Signatures.LinearFunctional.Proofs.Adaptive
import Signatures.OOPS.Proofs.SignatureHandle

/-! The recovered adaptive proof must not acquire admitted axioms during migration. -/

/-- info: 'AlgebraicGroupModel.LinFunctional.functional_euf_cma_adaptive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGroupModel.LinFunctional.functional_euf_cma_adaptive
