import Signatures.Runtime.SourceQueryBound

/-! Finite oracle families come from program syntax. In particular, a bounded
uniform command carries its arity as a literal; allocating tapes need not scan
every smaller arity. -/

open OracleComp OracleSpec

namespace Signatures.Runtime

variable {Atom : Type} {base : Atom → Type} {Op Cmd : Ty Atom → Ty Atom → Type}
  {I S : Type} {spec : OracleSpec.{0, 0} I}

/-- Collect only the families named by command implementations. Duplicates are
allowed here and can be removed when allocating the seed. -/
def Program.queryFamilies (labels : {a b : Ty Atom} → Cmd a b → List I) {Γ a} :
    Program Op Cmd Γ a → List I
  | .ret _ => []
  | .query cmd _ => labels cmd
  | .bind first next => first.queryFamilies labels ++ next.queryFamilies labels
  | .branch _ yes no => yes.queryFamilies labels ++ no.queryFamilies labels
  | .loop _ _ body => body.queryFamilies labels
  | .call body _ => body.queryFamilies labels

theorem allQueriesSatisfy_of_imp {A : Type} (main : OracleComp spec A)
    {p q : I → Prop} (h : AllQueriesSatisfy main p) (hpq : ∀ i, p i → q i) :
    AllQueriesSatisfy main q := by
  induction main using OracleComp.inductionOn with
  | pure _ => trivial
  | query_bind i next ih =>
      exact ⟨hpq i h.1, fun u => ih u (h.2 u)⟩

private theorem repeatDenote_allQueriesSatisfy {A : Type}
    (step : A → StateT S (OracleComp spec) A) (p : I → Prop)
    (h : ∀ a s, AllQueriesSatisfy ((step a).run s) p) (n : Nat) (a : A) (s : S) :
    AllQueriesSatisfy ((repeatDenote step n a).run s) p := by
  induction n generalizing a s with
  | zero => exact allQueriesSatisfy_pure _ _
  | succ n ih =>
      rw [repeatDenote, StateT.run_bind]
      exact allQueriesSatisfy_bind (h a s) fun out => ih out.1 out.2

/-- Every semantic query belongs to a family named in the source syntax. -/
theorem Program.denote_queryFamilies (P : Primitives base Op)
    (H : SemanticsM base Cmd (StateT S (OracleComp spec)))
    (labels : {a b : Ty Atom} → Cmd a b → List I)
    (hhandler : ∀ {a b} (cmd : Cmd a b) arg state,
      AllQueriesSatisfy ((H cmd arg).run state) (fun i => i ∈ labels cmd))
    {Γ a} (code : Program Op Cmd Γ a) (env : Env base Γ) (state : S) :
    AllQueriesSatisfy ((code.denote P H env).run state)
      (fun i => i ∈ code.queryFamilies labels) := by
  induction code generalizing state with
  | ret e => exact allQueriesSatisfy_pure _ _
  | query cmd arg => exact hhandler cmd _ state
  | bind first next ih ihnext =>
      rw [Program.denote, StateT.run_bind]
      apply allQueriesSatisfy_bind
      · exact allQueriesSatisfy_of_imp _ (ih env state) (by
          intro i hi; exact List.mem_append_left _ hi)
      · intro out
        exact allQueriesSatisfy_of_imp _ (ihnext (out.1, env) out.2) (by
          intro i hi; exact List.mem_append_right _ hi)
  | branch cond yes no ihyes ihno =>
      simp only [Program.denote]
      split
      · exact allQueriesSatisfy_of_imp _ (ihyes env state) (by
          intro i hi; exact List.mem_append_left _ hi)
      · exact allQueriesSatisfy_of_imp _ (ihno env state) (by
          intro i hi; exact List.mem_append_right _ hi)
  | loop count init body ih =>
      exact repeatDenote_allQueriesSatisfy _ _ (fun x s => ih (x, env) s) _ _ _
  | call body args ih => exact ih (args.denote P env) state

/-- A total path budget and a finite-family certificate give a seed budget
with zero capacity for every unused family. -/
theorem perIndexBound_of_total_families [DecidableEq I] {A : Type}
    (main : OracleComp spec A) (families : List I) (n : Nat)
    (htotal : IsTotalQueryBound main n)
    (hfamilies : AllQueriesSatisfy main (fun i => i ∈ families)) :
    IsPerIndexQueryBound main (fun i => if i ∈ families then n else 0) := by
  induction main using OracleComp.inductionOn generalizing n with
  | pure _ => exact isPerIndexQueryBound_pure _ _
  | query_bind i next ih =>
      rw [isTotalQueryBound_query_bind_iff] at htotal
      rw [allQueriesSatisfy_query_bind_iff] at hfamilies
      rw [isPerIndexQueryBound_query_bind_iff]
      refine ⟨by simpa [hfamilies.1] using htotal.1, fun u => ?_⟩
      apply (ih u (n - 1) (htotal.2 u) (hfamilies.2 u)).mono
      intro j
      by_cases hj : j = i
      · subst j; simp [hfamilies.1]
      · simp only [Function.update_of_ne hj]
        split <;> omega

end Signatures.Runtime
