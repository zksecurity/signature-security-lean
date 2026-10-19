/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan
-/
import AlgebraicGroupModel
import Signatures.Runtime.Caliper
import Signatures.Model.CoCDH
import Signatures.Model.LazyAGM
import Signatures.BLS.Statement
import Signatures.BLS.GeneralAGMFamilyStatement
import Signatures.BLS.Proofs.LazyAGMArbitraryMessages
import Signatures.BLS.Proofs.LazyAGMList
import Signatures.BLS.Proofs.LazyAGMCacheBound
import Signatures.Runtime.Caliper.BLSCache
import Signatures.Runtime.Caliper.BLSCacheReachability
import Signatures.Runtime.Caliper.BLSCachePairs
import Signatures.Runtime.Caliper.BLSResponseMemory
import Signatures.Runtime.Caliper.BLSRecordBounds
import Signatures.Runtime.Caliper.BLSRecordReachability
import Signatures.Runtime.Caliper.BLSOracleSchemes
import Signatures.Runtime.Caliper.BLSCallerPacketBounds
import Signatures.Runtime.Caliper.BLSCallerResources
import Signatures.Runtime.Caliper.BLSSetupResources
import Signatures.Runtime.Caliper.BLSChronological
import Signatures.Runtime.Caliper.ListIndexBounds
import Signatures.OOPS.Statement
import Signatures.OOPS.GeneralAGMFamilyStatement
import Signatures.OOPS.Proofs.LazyAGMArbitraryTopics
import Signatures.Proximity.Statement
import Signatures.Proximity.GeneralAGMFamilyStatement
import Signatures.Proximity.Proofs.LazyAGMArbitrarySlots
import Signatures.LinearFunctional.Proofs.LazyAGMCacheBound
import Signatures.Schnorr.Statement
import Signatures.Schnorr.GeneralAGMFamilyStatement
import Signatures.Schnorr.GeneralROMFamilyStatement
import Signatures.Schnorr.GeneralNonzeroROMFamilyStatement
import Signatures.Schnorr.BitStatement
import Signatures.Schnorr.SeededBitStatement
import Signatures.Schnorr.Proofs.NonzeroSecurity
import Signatures.Schnorr.Proofs.NonzeroLazyROM
import Signatures.Model.NonzeroFieldGrowth
import Signatures.Runtime.BackendSchnorrNonzeroSigningSource
import Signatures.Runtime.BackendSchnorrNonzeroRepairCost
import Signatures.Runtime.BackendSchnorrNonzeroSigningBudget
import Signatures.Runtime.SchnorrNonzeroListReduction
import Signatures.Runtime.SchnorrNonzeroListGrowth
import Signatures.Runtime.BackendSchnorrNonzeroPassPolynomial
import Signatures.Runtime.BackendSchnorrNonzeroPassDescription
import Signatures.Runtime.BackendSchnorrNonzeroSecurity
import Signatures.Runtime.BackendSchnorrNonzeroSolverPolynomial
import Signatures.Runtime.BackendSchnorrNonzeroDescriptionPolynomial
import Signatures.Runtime.BackendSchnorrNonzeroDescriptionAllowance
import Signatures.Schnorr.Proofs.AGMSecurity
import Signatures.Runtime.SchnorrAGMSecurity
import Signatures.Runtime.BackendSchnorrAGMReadBudget
import Signatures.Runtime.BackendSchnorrAGMFlattenBudget
import Signatures.Runtime.BackendSchnorrAGMHashBudget
import Signatures.Runtime.BackendListSingleton
import Signatures.Runtime.BackendSchnorrAGMHashDispatchBudget
import Signatures.Runtime.BackendListSnoc
import Signatures.Runtime.BackendSchnorrAGMProgramming
import Signatures.Runtime.BackendSchnorrAGMSigningBudget
import Signatures.Runtime.BackendSchnorrAGMSigningDispatchBudget
import Signatures.Runtime.BackendSchnorrAGMRandomBudget
import Signatures.Runtime.BackendSchnorrAGMHandlerDescription
import Signatures.Runtime.BackendSchnorrAGMHandlerPrimitiveBudget
import Signatures.Runtime.BackendSchnorrAGMCallerBudget
import Signatures.Runtime.BackendSchnorrAGMOutputSize
import Signatures.Runtime.BackendSchnorrAGMExtractionDescription
import Signatures.Runtime.BackendSchnorrAGMExtractionBudget
import Signatures.Runtime.BackendSchnorrAGMExtractionResources
import Signatures.Runtime.BackendSchnorrAGMSolverOutput
import Signatures.Runtime.BackendSchnorrAGMSolverCorrectness
import Signatures.Runtime.BackendSchnorrAGMSolverDescription
import Signatures.Runtime.BackendSchnorrAGMSolverSetup
import Signatures.Runtime.BackendSchnorrAGMSecurity
import Signatures.Runtime.SchnorrSeededSecurity
import Signatures.Runtime.SchnorrSeededPassBudget
import Signatures.Runtime.SeedTapeReset
import Signatures.Runtime.SchnorrLazySeedLog
import Signatures.Runtime.SeededDeferredTrace
import Signatures.Runtime.SeededSuffixSampling
import Signatures.Runtime.SeededForkReachability
import Signatures.Runtime.SchnorrLazyFork
import Signatures.Schnorr.Proofs.LazyROM
import Signatures.Runtime.SchnorrRawFork
import Signatures.Runtime.SchnorrRawTapeBounds
import Signatures.Runtime.BackendSchnorrRawUniformPolynomial
import Signatures.Runtime.BackendSchnorrRawChallengeBudget
import Signatures.Runtime.BackendSchnorrRawResetBudget
import Signatures.Runtime.BackendSchnorrRawLookupCost
import Signatures.Runtime.BackendSchnorrRawForkDescription
import Signatures.Runtime.BackendSchnorrRawForkBudget
import Signatures.Runtime.SchnorrROMListReduction
import Signatures.Runtime.SchnorrROMListGrowth
import Signatures.Runtime.BackendSchnorrROMCache
import Signatures.Runtime.BackendSchnorrROMLiveBudget
import Signatures.Runtime.BackendSchnorrROMProgrammingCost
import Signatures.Runtime.BackendSchnorrROMPrivateBudget
import Signatures.Runtime.BackendSchnorrROMHandlerDescription
import Signatures.Runtime.BackendSchnorrROMHandlerPrimitiveBudget
import Signatures.Runtime.BackendSchnorrROMHandlerPolynomial
import Signatures.Runtime.BackendSchnorrROMHandlerReserve
import Signatures.Runtime.BackendSchnorrROMCallerPolynomial
import Signatures.Runtime.BackendSchnorrROMCallerOutput
import Signatures.Runtime.BackendSchnorrROMPassSource
import Signatures.Runtime.BackendSchnorrROMPassDescription
import Signatures.Runtime.BackendSchnorrROMPassPolynomial
import Signatures.Runtime.BackendSchnorrROMSelectionPolynomial
import Signatures.Runtime.BackendSchnorrROMForkDescription
import Signatures.Runtime.BackendSchnorrROMForkPolynomial
import Signatures.Runtime.BackendSchnorrROMSolverDescription
import Signatures.Runtime.BackendSchnorrROMSolverPolynomial
import Signatures.Runtime.BackendSchnorrROMDescriptionPolynomial
import Signatures.Runtime.BackendSchnorrROMSecurity
import Signatures.Runtime.BackendSchnorrPrivateSamplingDescription
import Signatures.Runtime.BackendSchnorrPrivateSamplingBudget
import Signatures.Runtime.BackendSchnorrPrivateSamplingResources
import Signatures.Runtime.BackendStateSimulationResources
import Signatures.Runtime.BackendStateSimulationRouting
import Signatures.Runtime.BackendCoronSecurity
import Signatures.Runtime.BackendCoronPolynomial
import Signatures.Runtime.BackendCoronFamilySecurity
import Signatures.Runtime.BackendWeightedTerms
import Signatures.Runtime.BackendWeightedKeyEquality
import Signatures.Runtime.BackendWeightedCache
import Signatures.Runtime.BackendWeightedReadBudget
import Signatures.Runtime.BackendWeightedEvaluateDescription
import Signatures.Runtime.BackendWeightedGoodEvaluate
import Signatures.Runtime.BackendWeightedBadEvaluate
import Signatures.Runtime.BackendWeightedEvaluateEncoding
import Signatures.Runtime.BackendWeightedCoefficients
import Signatures.Runtime.BackendWeightedCoefficientBudget
import Signatures.Runtime.BackendWeightedHandlerBudget
import Signatures.Runtime.BackendWeightedHandlerDescription
import Signatures.Runtime.BackendWeightedOracle
import Signatures.Runtime.BackendWeightedReplyDescription
import Signatures.Runtime.BackendWeightedReplyCost
import Signatures.Runtime.BackendWeightedReplySize
import Signatures.Runtime.BackendWeightedHashBudget
import Signatures.Runtime.BackendWeightedSignBudget
import Signatures.Runtime.BackendWeightedOracleCallerBudget
import Signatures.Runtime.BackendWeightedOracleCallerResources
import Signatures.Runtime.BackendWeightedExtractionOutput
import Signatures.Runtime.BackendWeightedExtractionEntry
import Signatures.Runtime.BackendWeightedOracleCache
import Signatures.Runtime.BackendWeightedOracleDescription
import Signatures.Runtime.BackendWeightedExtractionDescription
import Signatures.Runtime.BackendWeightedExtractionState
import Signatures.Runtime.BackendWeightedSigningExtraction
import Signatures.Runtime.BackendWeightedHashExtraction
import Signatures.Runtime.BackendWeightedTargetExtraction
import Signatures.Runtime.BackendWeightedGoodExtractionBudget
import Signatures.Runtime.BackendWeightedBadExtractionBudget
import Signatures.Runtime.BackendWeightedSolverWithin
import Signatures.Runtime.BackendWeightedScale
import Signatures.OperationBounds
import Signatures.PaperStatements

/-!
# Signature security: lazy games and security proofs

The pinned `agm-lean` library takes a game-chosen oracle interface and finite input
transcript. Hashing, signing, pairing verification, and freshness belong to the signature
protocol, not to the generic representation interface.
`Interaction` additionally supports explained group arguments in adaptive oracle calls and
multiple final group outputs, with exact plain-computation erasure and received-basis tracking.
The three pairing-based AGM signature games accept that shared adversary directly and
execute its certified runner in `Model.DirectAGM`. Their requests have no group arguments;
replies extend the basis and the final forgery is explained. An internally derived
coefficient view preserves execution and query counts. Rejecting malformed protocol
messages gives a win-probability inequality to the existing extraction proofs;
Proximity's collision event is preserved exactly. Caller budgets include producing the
derived coefficient encoding.

Seven general-attacker routes cover BLS co-CDH, BLS/OOPS/Proximity AGM, Schnorr
AGM and both Schnorr ROM nonce conventions. Their concrete and nonuniform family
statements derive complete runtime/code certificates in one fixed backend.
Hashing, signing and verification share a lazy cache; only AGM routes require
algebraic outputs. Proximity retains its actual collision term.
The superseded eager-table AGM security wrappers have been retired. Original
probability definitions and resource lemmas remain for reference and exact
lazy/eager coupling. Arithmetic-source BLS co-CDH and Schnorr statements retain
their separate scopes; Schnorr also has a bit-heap endpoint with sampling error.
The BLS co-CDH route additionally has `Coron.NativeSolver.security_of_resources`:
arbitrary realized caller code in a fixed quantitative backend, a complete native
solver certificate derived from caller and primitive contracts, and explicit
input/runtime/stored-code hardness budgets. Its numerical runtime and description
bounds preserve polynomial growth under fixed polynomial resource contracts.
The concrete and nonuniform-family endpoints allow arbitrary message types.
The BLS AGM route now has complete lazy native runtime/code certificates and
`LazyAGM.NativeSolver.security_of_resources` in the same fixed backend. Its short
public theorem is `BLS.agm_security`, with curve, security parameter, query allowances,
and algebraic adversary as its four explicit inputs. `BLS.cocdh_security` gives
the unrestricted co-CDH route in the same form, with its own attacker/model class.
The main AGM bound is twice the DLog advantage at the larger derived reduction
time plus `1/|F|`; `BLS.agm_security_two_budgets` retains the sharper separate times.
Parameters expose query/resource limits and primitive contracts in separate
`AGMSecurityModel` and `CoCDHSecurityModel` records,
while the adversary supplies its actual general realization. The AGM asymptotic
corollary `BLS.GeneralAGM.Family.security_asymptotic` derives polynomial solver
time/code bounds from component resources, then applies nonuniform DLog hardness
and negligible inverse field size in one backend fixed across parameters.
A conventional-machine adequacy theorem remains separate from this conditional
fixed-backend result.
`OperationBounds` supplies concrete operation ledgers for all four routes with exact solver
erasure. AGM source certificates include local work and output sizes. The bad-branch package
also charges both full-domain scalar tables, masked bases, and public-key construction.

The AGM bounds combine hardness for two DLog reductions plus `1/|F|`. OOPS restricts distinct messages on the
eventual target topic; Proximity adds the actual fresh-collision probability. BLS/co-CDH uses the
lazy Coron reduction with a signing-call budget.

Public-table source variants have been removed. Private finite tables remain inside the
AGM reductions and lazy/eager proof coupling; they are never given to the source adversary.
The new BLS AGM lazy solvers have joint probability correspondence, sparse extraction,
finite-list cache refinement, structural query/storage bounds, and the same
probability theorem for arbitrary messages, now composed with complete runtime/code
certificates and general callers. The original AGM machine certificates
remain valid for the eager solvers as supporting reference lemmas, not public
efficiency endpoints. See `docs/API-MIGRATION.md`.
OOPS and Proximity also have weighted lazy list-cache reductions, joint
distribution equality with their existing eager solvers, and corresponding
probability bounds for arbitrary topic/slot types. Both branches use at most
`qH + (qS + 1) * L` cache entries (`L = d + 1` or `ell + 1`); extraction is proved
to reread cached entries without fresh sampling. The finite topic/slot covers
are proof artifacts over generated keys and all reply paths; exact transport
preserves each source game and Proximity's collision term. The weighted term
generators have actual native code, exact source semantics, and derived runtime,
stored-code, and output-size bounds. Both native weighted scalar/pair evaluators
now have complete derived runtime/code and encoded-result/cache bounds, charging
indexed row scans, cache growth, reads, arithmetic and loop control. Weighted
evaluation preserves the original source indices and complete cache under
injective encodings. Native signing-coefficient expansion has exact source
semantics and complete runtime, stored-code and output-size bounds. Its runtime
charges chronological matching, term generation in retained contexts, scaling,
both expansion folds and final reversal. Weighted request dispatch now supports
distinct hash-index/signing-message types, with exact general-caller semantics
and derived routing/runtime/stored-code bounds. Both actual weighted hash/sign
branches are installed, with exact general-caller/source correspondence, complete
stored-code bounds, and complete reply runtime bounds. Preserved cache/log capacities
now compose these with native dispatch and general-caller runtime/code bounds.
Both native extractors now have exact source/cache correspondence, complete
stored-code bounds, and final-target-only cache growth. All five extraction
calls now have derived runtime bounds for hash/sign transcripts and both final-target
branches. Complete outer extractor runtime bounds now compose these calls with
default construction, final arithmetic, and the retained output and transcripts.
They derive all component costs from primitive contracts and the cached-transcript
invariant. Request sizes, caller reachability, returned-output/coefficient bounds,
and the extractor's input widths now follow from general attacker resources and
encoding contracts. Exact native interaction semantics supplies the cached-transcript
invariant from an empty store. Both complete weighted solvers now have derived
runtime/code certificates and general-caller concrete and nonuniform family
security endpoints. OOPS retains admissibility; Proximity retains its collision loss.

Schnorr's two-pass machine re-executes the source with a recorded prefix. Its certificate
charges both passes, caches, replay tape, scans, verification, extraction, and fixed data;
exact query-tree equality connects it to VCVio's named Schnorr reduction.
Its bit backend includes input loading and all online operations, with runtime
`(targetBudget + 4) * bitFactor` and additive sampling loss `targetBudget * 2^(-k)`.
The fully seeded variant fixes every private family across both passes. Its
complete controller has exact equality to the source-derived seeded reduction,
an arithmetic budget from the original source certificate, and a bit-hardness
endpoint covering setup, both passes and sampling error. A separate nonzero-nonce
ROM theorem proves exact finite simulation and the signing collision loss with
denominator |F|-1. The adaptive Schnorr AGM solver has representation invariants,
pathwise extraction, and security for the original source game. Its bound includes
the (qH+1)/|F| exceptional-challenge term and qS*(qS+qH)/|F| signing-simulation loss.
Its finite-list implementation now preserves the complete adaptive output/state
query tree and the original probability bound. It stores at most qS+qH+1 cached
pairs, qS+2 affine basis entries, and qS signed messages, over arbitrary message
and group types. Native tuple/list layouts and cache-core code now have exact
source correspondence, complete runtime and stored-code bounds. Cache misses
retain the pre-challenge explanation as represented input and update bad using
field instructions; hits skip sampling entirely. Complete native reads also
construct the default entry and route the whole state, with derived time/code
bounds and unchanged history-size limits. Native representation flattening now
preserves chronological coefficients and zero padding, with derived time/code
and output-size bounds including the entire coefficient list and retained context.
The decoded singleton hash path composes flattening and the complete read, with
derived preparation/control/time/code bounds and exact source correspondence.
The all-shape hash dispatcher now charges both singleton scans, default creation,
branch selection and malformed-state construction. It agrees with the source
handler at its scalar/state interface, and rejection never calls the sampler.
The signing dispatcher now handles every request shape, constructs scalar/group-list
replies and charges both accepted and rejected paths, including ignored coefficient
rows. Random handling makes one runtime-selected uniform query even for malformed
requests, with derived conversion, scan, state and reply costs. The complete native
dispatcher now installs all three handlers with request retention and indexed
reply tagging. General callers have exact adaptive source correspondence and
complete stored-code bounds. Indexed handler/caller runtime is derived from
primitive contracts and measured attacker resources. The native final extractor
has exact scalar/state source semantics and complete runtime/stored-code bounds
for every output shape. Its input bounds follow from the full encoded return and
caller state. Actual output conversion now has runtime and stored-code bounds,
including retained state. The complete native solver now assembles setup, caller,
cutoff handling, extraction and scalar projection, with exact source correspondence
and a complete stored-code bound. Setup, cutoff and projection have derived runtime
bounds. The complete terminal and solver runtime now follow from primitive and
representation contracts and measured caller resources. A fixed-backend executable
witness combines runtime, full stored-code accounting and exact source behavior;
the concrete security theorem applies DLog hardness to this witness with the
original probability losses. `Schnorr.agm_security` exposes the short public
statement. Polynomial closure of the complete native time/code formulas and
`Schnorr.GeneralAGM.Family.security_asymptotic` are proved in one fixed backend,
under polynomial component resources, DLog hardness and negligible inverse field
size. General-caller full-field ROM replay is also complete. The nonzero-nonce
variant has a complete native signing budget, finite-cache pass correspondence,
cache capacities and exact finite replay/extraction semantics. Its installed
private samplers and common-store signer now have exact source correspondence
and complete runtime/code bounds, with polynomial closure from original resources.
The nonzero dispatcher, arbitrary caller and complete native pass now also have
exact source correspondence, derived runtime/code/output bounds and polynomial
runtime closure from original resources. Both actual passes now compose into the
complete replaying solver, with exact source correspondence, derived runtime/code
bounds, polynomial closure and a fixed-backend executable certificate. The concrete
DLog-hardness endpoint preserves the nonzero signing loss. The short public
`Schnorr.NonzeroNonce.rom_security` statement and its nonuniform family corollary
now derive security from those certificates. The family proof uses polynomial
original resources and the same negligible inverse-field-size assumption.

The public security statements' axiom footprints are exactly
`propext`, `Classical.choice`, and `Quot.sound`.
No conventional-machine PPT preservation, standard-model OOPS result, concrete-hash instantiation, or equivalence
to ArkLib's experimental runner is claimed. See `docs/review-guide.md` for the GitHub review path.
-/
