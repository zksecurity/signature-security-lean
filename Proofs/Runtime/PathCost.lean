import Proofs.Runtime.QueryCost
import VCVio.CryptoFoundations.ReplayFork

/-! Intrinsic paths realize weighted query counts. Exact state accounting can
therefore establish that a selected fork ordinal actually occurred. -/

open OracleComp OracleSpec PFunctor.FreeM

namespace Signatures.Runtime

variable {I A : Type} {spec : OracleSpec.{0, 0} I} [DecidableEq I]

attribute [local implicit_reducible] PFunctor.Idx FreeMonoid

theorem QueryCost.of_path (target : I) (main : OracleComp spec A) (path : Path main) :
    QueryCost (fun i => if i = target then 1 else 0) main (output main path)
      (PFunctor.TraceList.occurrences target (Path.trace main path)) := by
  induction main with
  | pure a => exact .pure a
  | queryBind i next ih =>
      rcases path with ⟨reply, tail⟩
      have h := QueryCost.queryBind i next reply (ih reply tail)
      by_cases hi : i = target <;>
        simpa [Path.trace, output, PFunctor.TraceList.occurrences, hi, Nat.add_comm] using h

theorem pathCfReachable_of_queryCost (main : OracleComp spec A) (qb : I → Nat) (target : I)
    (select : A → Option (Fin (qb target + 1)))
    (h : ∀ out n, QueryCost (fun i => if i = target then 1 else 0) main out n →
      ∀ slot, select out = some slot → slot.val < n) :
    PathCfReachable main qb target select := by
  intro path slot hselect
  rw [Cursor.locateAt?_isSome_iff_lt_occurrences]
  exact h _ _ (QueryCost.of_path target main path) slot hselect

end Signatures.Runtime
