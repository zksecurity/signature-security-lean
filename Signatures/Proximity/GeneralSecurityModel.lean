import Signatures.Proximity.Game
import Signatures.Proximity.CaliperAGMParameters

/-! Inspectable games, DLog reductions and their Caliper budget for Proximity. The mathematical
curve and dimension stay explicit. Fixed local implementations, encodings and
caller allowances determine both complete reduction time, code and memory bounds.
The game stays independent of these implementation contracts. -/

open OracleComp OracleSpec PFunctor
open Signatures.Runtime

namespace Proximity

abbrev QueryAllowance := WeightedCaliper.QueryAllowance

/-- Caliper layouts, local implementations and caller allowances, fixed before
choosing the attacker. Complete reduction code and bounds are constructed from
these components; no completed-solver contract or hardness assumption is a field. -/
class AGMSecurityModel (curve : Model.PairingCurve) where
  Slot : Nat → Type
  [slotEquality : ∀ n, DecidableEq (Slot n)]
  parameters : ∀ n dimension q, CaliperAGM.Parameters
    (curve.Scalar n) (curve.SignatureGroup n) (curve.KeyGroup n) (Slot n)
    dimension q (curve.generator n) (curve.keyGenerator n)

attribute [instance_reducible, instance] AGMSecurityModel.slotEquality

variable (curve : Model.PairingCurve) [model : AGMSecurityModel curve]

/-- An arbitrary realized algebraic attacker within the model's own execution,
stored-code, memory and per-kind query limits. Local code is general Caliper
code; conventional-machine coverage remains a separate adequacy claim. The source retains the original vector/slot game interface. -/
abbrev AlgebraicAdversary (securityParameter dimension : Nat) (queries : QueryAllowance) :=
  WeightedCaliper.AlgebraicAdversary (model.parameters securityParameter dimension queries)

/-- Maximum of the two complete runtime bounds proved for the constructed solvers. -/
def agmReductionTime (securityParameter dimension : Nat) (queries : QueryAllowance) : Nat :=
  let resources := model.parameters securityParameter dimension queries
  max resources.goodTime resources.badTime

/-- The actual lazy EUF-CMA experiment, with shared hash/signing/verification
bases. Fresh collisions remain wins when the signature verifies; they are not rejected.
The secret is uniform over the whole field, including zero. -/
noncomputable def agmEufCmaGame (securityParameter dimension : Nat) {queries : QueryAllowance}
    (adversary : AlgebraicAdversary curve securityParameter dimension queries) : ProbComp Bool :=
  Game.agm curve securityParameter dimension adversary.source

/-- Actual fresh-collision probability in the same source interaction. Every
signed vector, including repetitions and other slots, contributes with its
returned signing coefficient. Missing coefficients are zero. This event does
not require a valid signature and is not assumed negligible. -/
noncomputable def freshCollisionGame (securityParameter dimension : Nat) {queries : QueryAllowance}
    (adversary : AlgebraicAdversary curve securityParameter dimension queries) : ProbComp Bool :=
  Game.collision curve securityParameter dimension adversary.source

/-- The first `(1,1)`-DLog solver built from the attacker: it uses the challenge
`x • g₁` as the signing key, answers hashes with known multiples of `g₁`, and
solves for `x` from the forgery's algebraic explanation. Its Caliper
implementation is in `Proofs/Runtime/Caliper/WeightedGood.lean`. -/
noncomputable def agmGoodReduction {securityParameter dimension : Nat} {queries : QueryAllowance}
    (adversary : AlgebraicAdversary curve securityParameter dimension queries) :
    AlgebraicGroupModel.DLog11Adversary (curve.Scalar securityParameter)
      (curve.SignatureGroup securityParameter) (curve.KeyGroup securityParameter) :=
  Model.LazyAGM.WeightedReduction.goodReductionList LazyAGM.terms adversary.proofView

/-- The second solver, for forgeries the first cannot use: it samples the signing
key itself, embeds the challenge in every hash answer, and solves for `x` from
the forgery's explanation. Its Caliper implementation is in
`Proofs/Runtime/Caliper/WeightedBad.lean`. -/
noncomputable def agmBadReduction {securityParameter dimension : Nat} {queries : QueryAllowance}
    (adversary : AlgebraicAdversary curve securityParameter dimension queries) :
    AlgebraicGroupModel.DLog11Adversary (curve.Scalar securityParameter)
      (curve.SignatureGroup securityParameter) (curve.KeyGroup securityParameter) :=
  Model.LazyAGM.WeightedReduction.badReductionList LazyAGM.terms adversary.proofView

/-- A `(1,1)`-DLog solver given `(g₁, x • g₁, g₂, x • g₂)` that runs as Caliper
code on the fixed port and layouts within the derived code and total-memory
limits and the displayed time limit. Memory includes the stored program, input
and every intermediate state, and every sampled challenge must be representable. -/
def DLog11SolverWithin (securityParameter dimension : Nat) (queries : QueryAllowance) (time : Nat)
    (solver : AlgebraicGroupModel.DLog11Adversary (curve.Scalar securityParameter)
      (curve.SignatureGroup securityParameter) (curve.KeyGroup securityParameter)) : Prop :=
  (model.parameters securityParameter dimension queries).within time solver

end Proximity
