import Proofs.Schnorr.CaliperAGMCaller
import Proofs.Runtime.Caliper.SchnorrAGMSourceAdversary

/-! Construct the algebraic source as well as its machine presentation from
local Caliper code. Callers supply local resource, query and algebraicity proofs;
no independent source adversary or source-equivalence certificate is required. -/
namespace Schnorr.CaliperAGM
open Caliper OracleComp OracleSpec Signatures.Runtime Signatures.Runtime.CaliperBackend BoundedSource
open Signatures.Runtime.SchnorrAGM.Native
variable {F G M : Type} [Field F] [SampleableType F] [AddCommGroup G] [Module F G]
    [DecidableEq F] [DecidableEq G] [DecidableEq M]
    {queries : QueryAllowance} {generator : G}
    (P : Parameters F G M queries generator)
    (caller : CaliperBackend.SchnorrAGM.Full.Caller P.layout)

/-- Query allowances for all represented reply branches, including termination. -/
structure LocalQueries : Prop where
  random : CaliperBackend.SchnorrAGM.Full.Caller.Partial.QueryBound P.layout caller
    (fun q => randomRequest q = true) queries.random queries.total
  hash : CaliperBackend.SchnorrAGM.Full.Caller.Partial.QueryBound P.layout caller
    (fun q => AGM.Reduction.hashRequest q = true) queries.hash queries.total
  sign : CaliperBackend.SchnorrAGM.Full.Caller.Partial.QueryBound P.layout caller
    (fun q => AGM.Reduction.signRequest q = true) queries.sign queries.total

/-- Outgoing groups have explanations over the actual received basis. The basis
is a proof parameter; the caller's executed code and state are unchanged. -/
def LocalAlgebraic : Prop := ∀ value,
  CaliperBackend.SchnorrAGM.Full.Caller.Partial.LocallyAlgebraic P.layout caller queries.total
    (AGM.initial value.val.1 value.val.2).groups (caller.initial value)

variable (allowances : LocalQueries P caller)

def LocalQueries.invariant : CaliperBackend.SchnorrAGM.Full.Caller.Invariant P.layout caller queries.total :=
  CaliperBackend.SchnorrAGM.Full.Caller.Partial.invariant P.layout caller allowances.hash allowances.sign

omit [DecidableEq F] [DecidableEq G] [DecidableEq M] in
include allowances in
theorem LocalQueries.terminates :
    CaliperBackend.SchnorrAGM.Full.Caller.Partial.Terminates P.layout caller queries.total :=
  CaliperBackend.SchnorrAGM.Full.Caller.Partial.QueryBound.terminates _ _ _ _ allowances.random

/-- A terminating represented execution supplies a represented data payload.
Clearing its group lists gives a source-only fallback valid at every basis. -/
noncomputable def LocalQueries.fallback : P.layout.forgery.Value :=
  CaliperBackend.SchnorrAGM.Full.Caller.Partial.blank P.layout
    (Classical.choice (CaliperBackend.SchnorrAGM.Full.Caller.Partial.forgery_nonempty P.layout caller
      (allowances.terminates P caller) P.routines.handler.zeroValid
      ⟨(generator, generator), P.generatorValid, P.generatorValid⟩))

omit [DecidableEq F] [DecidableEq G] [DecidableEq M] in
theorem LocalQueries.fallback_valid (basis : AlgebraicGroupModel.Interaction.Groups (AGM.Group G)) :
    (Interface.decodeForgery (allowances.fallback P caller).val).Valid basis :=
  CaliperBackend.SchnorrAGM.Full.Caller.Partial.blank_valid P.layout _ basis

/-- Build all source and machine certificates from the caller's local contracts. -/
noncomputable def AlgebraicAdversary.ofLocalCaller
    (resources : CaliperBackend.SchnorrAGM.Full.Caller.Bounds P.layout caller P.callerLimits)
    (algebraic : LocalAlgebraic P caller) : AlgebraicAdversary P where
  source := CaliperBackend.SchnorrAGM.Full.Caller.Partial.adversary P.layout caller
    (allowances.fallback P caller) queries.total (allowances.fallback_valid P caller) algebraic
  caller := caller
  invariant := allowances.invariant P caller
  correspondence := CaliperBackend.SchnorrAGM.Full.Caller.Partial.correspondence P.layout caller
    (allowances.fallback P caller) (allowances.invariant P caller) (allowances.terminates P caller)
  source_eq := fun value => (CaliperBackend.SchnorrAGM.Full.Caller.Partial.main_initial
    P.layout caller (allowances.fallback P caller) queries.total value).symm
  bounds := resources
  randomQueries := fun pk => CaliperBackend.SchnorrAGM.Full.Caller.Partial.main_queryBound
    P.layout caller (allowances.fallback P caller) queries.total _ _ allowances.random (AGM.initial generator pk)
  hashQueries := fun pk => CaliperBackend.SchnorrAGM.Full.Caller.Partial.main_queryBound
    P.layout caller (allowances.fallback P caller) queries.total _ _ allowances.hash (AGM.initial generator pk)
  signingQueries := fun pk => CaliperBackend.SchnorrAGM.Full.Caller.Partial.main_queryBound
    P.layout caller (allowances.fallback P caller) queries.total _ _ allowances.sign (AGM.initial generator pk)

end Schnorr.CaliperAGM
