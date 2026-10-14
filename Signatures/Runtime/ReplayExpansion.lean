import Signatures.Runtime.ReplayKernel

/-! Expanding a private random-sampling primitive preserves the complete fork law.
Private implementations may use multiple raw queries but must not call the fork target. -/

open OracleComp OracleSpec

namespace Signatures.Runtime.Replay

variable {I J A F : Type} {spec : OracleSpec.{0, 0} I} {rawSpec : OracleSpec.{0, 0} J}
  [DecidableEq I] [DecidableEq J]

def expandPrivate (privateImpl : QueryImpl spec (OracleComp (rawSpec + (Unit →ₒ F)))) :
    QueryImpl (spec + (Unit →ₒ F)) (OracleComp (rawSpec + (Unit →ₒ F)))
  | .inl i => privateImpl i
  | .inr () => liftM ((rawSpec + (Unit →ₒ F)).query (.inr ()))

omit [DecidableEq I] [DecidableEq J] in
private theorem simulate_queryBind {B : Type} (impl : QueryImpl spec (OracleComp rawSpec))
    (i : I) (next : spec.Range i → OracleComp spec B) :
    simulateQ impl (OracleComp.queryBind i next) =
      impl i >>= fun answer => simulateQ impl (next answer) := by
  change simulateQ impl ((spec.query i : OracleComp spec _) >>= next) = _
  simp only [simulateQ_bind, simulateQ_spec_query]

set_option backward.isDefEq.respectTransparency false in
/-- Expansion does not resample the shared prefix independently in the two runs.
The equality includes the original focused answer, fresh focused answer and both outputs. -/
theorem forkKernel_expand
    (privateImpl : QueryImpl spec (OracleComp (rawSpec + (Unit →ₒ F))))
    (hprivate : ∀ i, IsQueryBoundP (privateImpl i) (fun j => j = Sum.inr ()) 0)
    (main : OracleComp (spec + (Unit →ₒ F)) A) (select : A → Option Nat) :
    simulateQ (expandPrivate privateImpl) (forkKernel (.inr ()) main select) =
      forkKernel (.inr ()) (simulateQ (expandPrivate privateImpl) main) select := by
  induction main using OracleComp.inductionOn generalizing select with
  | pure value => simp only [forkKernel_pure, simulateQ_pure]
  | query_bind i next ih =>
    change simulateQ (expandPrivate privateImpl)
      (forkKernel (.inr ()) (OracleComp.queryBind i next) select) =
        forkKernel (.inr ())
          (simulateQ (expandPrivate privateImpl) (OracleComp.queryBind i next)) select
    cases i with
    | inl i =>
      rw [forkKernel_other (spec := spec + (Unit →ₒ F)) (Sum.inr ()) (Sum.inl i)
        (by simp), simulate_queryBind, simulate_queryBind]
      simp only [expandPrivate]
      rw [forkKernel_private_bind _ _ (hprivate i)]
      congr 1
      funext answer
      exact ih answer select
    | inr u =>
      cases u
      rw [forkKernel_target, simulate_queryBind, simulate_queryBind]
      simp only [expandPrivate]
      change ((rawSpec + (Unit →ₒ F)).query (.inr ()) :
        OracleComp (rawSpec + (Unit →ₒ F)) F) >>= _ =
        forkKernel (.inr ()) (OracleComp.queryBind (.inr ())
          (fun answer => simulateQ (expandPrivate privateImpl) (next answer))) select
      rw [forkKernel_target]
      change OracleComp.queryBind (spec := rawSpec + (Unit →ₒ F)) (Sum.inr ())
        (fun answer => simulateQ (expandPrivate privateImpl) (do
          let first ← forkKernel (Sum.inr ()) (next answer) (fun x => previous (select x))
          if select first.1 = some 0 then do
            let fresh ← (spec + (Unit →ₒ F)).query (.inr ())
            let second ← next fresh
            pure (first.1, some (answer, fresh, second))
          else pure first)) = _
      apply congrArg (OracleComp.queryBind (spec := rawSpec + (Unit →ₒ F)) (Sum.inr ()))
      funext answer
      rw [simulateQ_bind, ih answer]
      congr 1
      funext first
      split <;> simp [simulateQ_bind, simulateQ_pure, expandPrivate]

/-- In particular, the guarded accepted-output law is unchanged by expanding private
samplers. No one-query implementation assumption on those samplers appears here. -/
theorem contextFork_expand [DecidableEq F]
    [∀ i, DecidableEq (spec.Range i)] [∀ j, DecidableEq (rawSpec.Range j)]
    (privateImpl : QueryImpl spec (OracleComp (rawSpec + (Unit →ₒ F))))
    (hprivate : ∀ i, IsQueryBoundP (privateImpl i) (fun j => j = Sum.inr ()) 0)
    (main : OracleComp (spec + (Unit →ₒ F)) A) (q : Nat)
    (select : A → Option (Fin (q + 1))) :
    simulateQ (expandPrivate privateImpl) (contextFork main (fun _ => q) (.inr ()) select) =
      contextFork (simulateQ (expandPrivate privateImpl) main) (fun _ => q) (.inr ()) select := by
  rw [← forkKernel_eq_contextFork, ← forkKernel_eq_contextFork]
  rw [simulateQ_map, forkKernel_expand privateImpl hprivate]

end Signatures.Runtime.Replay
