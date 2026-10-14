/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan
-/
import AlgebraicGroupModel
import Signatures.Model.CoCDH
import Signatures.Model.LazyAGM
import Signatures.BLS.Statement
import Signatures.BLS.Proofs.LazyAGMArbitraryMessages
import Signatures.BLS.Proofs.LazyAGMList
import Signatures.OOPS.Statement
import Signatures.OOPS.Proofs.LazyAGMArbitraryTopics
import Signatures.Proximity.Statement
import Signatures.Proximity.Proofs.LazyAGMArbitrarySlots
import Signatures.LinearFunctional.Proofs.LazyAGMCacheBound
import Signatures.Schnorr.Statement
import Signatures.Schnorr.BitStatement
import Signatures.Schnorr.SeededBitStatement
import Signatures.Schnorr.Proofs.NonzeroSecurity
import Signatures.Schnorr.Proofs.AGMSecurity
import Signatures.Runtime.SchnorrSeededSecurity
import Signatures.Runtime.SchnorrSeededPassBudget
import Signatures.Runtime.SeedTapeReset
import Signatures.Runtime.BackendCoronSecurity
import Signatures.Runtime.BackendCoronPolynomial
import Signatures.Runtime.BackendCoronFamilySecurity
import Signatures.OperationBounds
import Signatures.PaperStatements

/-!
# Signature security: lazy games and security proofs

The pinned `agm-lean` library takes a game-chosen oracle interface and finite input
transcript. Hashing, signing, pairing verification, and freshness belong to the signature
adapter, not to the generic representation interface.
`Interaction` additionally supports explained group arguments in adaptive oracle calls and
multiple final group outputs, with exact plain-computation erasure and received-basis tracking.
The three AGM signature games execute through its certified runner via `SignatureInteraction`.
Their requests have no group arguments; replies extend the basis and the final forgery is explained.
Exact computation equality preserves the existing security statements and named reductions.

Five security routes: BLS to co-CDH, BLS/OOPS/Proximity in the query-only lazy AGM,
and ordinary Schnorr ROM security to DLog with a complete costed replay machine.
Hashing, signing, and verification share a cache; algebraic outputs use only explicit replies.
Each exposes a concrete arithmetic-machine security statement; Schnorr also has
a bit-heap-machine endpoint with bounded-sampling error. The statements derive every named solver's budget from a source-code certificate, including local
work, fixed data, adaptive queries, cache/table operations, setup, and extraction. Both AGM
branches have complete closed-machine certificates.
The BLS co-CDH route additionally has `Coron.NativeSolver.security_of_resources`:
arbitrary realized caller code in a fixed quantitative backend, a complete native
solver certificate derived from caller and primitive contracts, and explicit
input/runtime/stored-code hardness budgets. Its numerical runtime and description
bounds preserve polynomial growth under fixed polynomial resource contracts.
The concrete and nonuniform-family endpoints allow arbitrary message types.
The BLS AGM route now has complete lazy native runtime/code certificates and
`LazyAGM.NativeSolver.security_of_resources` in the same fixed backend. Its short
public theorem is `BLS.security`, with curve, security parameter, query allowances,
and algebraic adversary as its four explicit inputs. The bound is
the sum of two resource-indexed DLog advantage bounds and `1/|F|`. Parameters
expose query/resource limits and primitive contracts in a separate `SecurityModel`,
while the adversary supplies its actual general realization. The AGM asymptotic
corollary remains separate.
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
above continue to apply to the eager solvers.
OOPS and Proximity also have weighted lazy list-cache reductions, joint
distribution equality with their existing eager solvers, and corresponding
probability bounds for arbitrary topic/slot types. Both branches use at most
`qH + (qS + 1) * L` cache entries (`L = d + 1` or `ell + 1`); extraction is proved
to reread cached entries without fresh sampling. The finite topic/slot covers
are proof artifacts over generated keys and all reply paths; exact transport
preserves each source game and Proximity's collision term. Complete native
weighted runtime/code bounds remain open.

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
Its complete runtime and general-caller composition remain open.

The public security statements' axiom footprints are exactly
`propext`, `Classical.choice`, and `Quot.sound`.
No PPT preservation, standard-model OOPS result, concrete-hash instantiation, or equivalence
to ArkLib's experimental runner is claimed. See `docs/review-guide.md` for the GitHub review path.
-/
