/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan
-/
import Signatures.OOPS.Statement

/-! Migration import for the retired eager-table arithmetic AGM endpoint.
Use `OOPS.agm_security` from `Statement.lean` (two separate DLog budgets: `OOPS.Proofs.agm_security`).
These quantify over general implemented algebraic attackers and use derived lazy
solver resources. The old eager wrapper is no longer declared. Supporting
probability/resource lemmas remain available; see `docs/API-MIGRATION.md`.
-/
