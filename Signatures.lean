/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan
-/
import AlgebraicGroupModel
import Signatures.Model.CoCDH
import Signatures.Model.LazyAGM
import Signatures.BLS.Statement
import Signatures.OOPS.Statement
import Signatures.Proximity.Statement
import Signatures.OperationBounds
import Signatures.PaperStatements

/-!
# Pairing-based signatures: lazy games and security proofs

The pinned `agm-lean` library takes a game-chosen oracle interface and finite input
transcript. Hashing, signing, pairing verification, and freshness belong to the signature
adapter, not to the generic representation interface.
`Interaction` additionally supports explained group arguments in adaptive oracle calls and
multiple final group outputs, with exact plain-computation erasure and received-basis tracking.
The three AGM signature games execute through its certified runner via `SignatureInteraction`.
Their requests have no group arguments; replies extend the basis and the final forgery is explained.
Exact computation equality preserves the existing security statements and named reductions.

Four public security endpoints: BLS to co-CDH, and BLS/OOPS/Proximity in the query-only lazy AGM.
Hashing, signing, and verification share a cache; algebraic outputs use only explicit replies.
Each exposes only its concrete arithmetic-machine security statement; weaker public wrappers
have been removed. The statements derive every named solver's budget from a source-code certificate, including local
work, fixed data, adaptive queries, cache/table operations, setup, and extraction. Both AGM
branches have complete closed-machine certificates.
`OperationBounds` supplies concrete operation ledgers for all four routes with exact solver
erasure. AGM source certificates include local work and output sizes. The bad-branch package
also charges both full-domain scalar tables, masked bases, and public-key construction.

The AGM bounds combine hardness for two DLog reductions plus `1/|F|`. OOPS restricts distinct messages on the
eventual target topic; Proximity adds the actual fresh-collision probability. BLS/co-CDH uses the
lazy Coron reduction with a signing-call budget.

Public-table source variants have been removed. Private finite tables remain inside the
AGM reductions and lazy/eager proof coupling; they are never given to the source adversary.
The lazy source definitions allow infinite index types, but the current security bounds do not.

All four public security statements' axiom footprints are exactly
`propext`, `Classical.choice`, and `Quot.sound`.
No PPT preservation, standard-model OOPS result, concrete-hash instantiation, or equivalence
to ArkLib's experimental runner is claimed. See `docs/review-guide.md` for the GitHub review path.
-/
