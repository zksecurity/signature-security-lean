import Signatures.Runtime.SourceBudget
import Signatures.Runtime.QueryCost
import Signatures.Runtime.ProgramSimulation
import Signatures.Runtime.Refinement

/-! Source certificates imply structural oracle-query bounds. This bridge is
pathwise and uses the source certificate itself, before any reduction is built. -/

open OracleComp OracleSpec

namespace Signatures.Runtime

attribute [local implicit_reducible] requestSpec

private def withUnitState {I : Type} {spec : OracleSpec I} :
    OracleComp spec →ᵐ StateT Unit (OracleComp spec) where
  toFun {_} main state := (fun out => (out, state)) <$> main
  toFun_pure' value := by
    funext state
    change (fun out => (out, state)) <$> (pure value : OracleComp spec _) = pure (value, state)
    simp
  toFun_bind' main next := by
    funext state
    change (fun out => (out, state)) <$> (main >>= next) =
      ((fun out => (out, state)) <$> main) >>= fun pair =>
        (fun out => (out, pair.2)) <$> next pair.1
    simp [map_bind, bind_map_left]

variable {Atom : Type} {base : Atom → Type} {Op Cmd : Ty Atom → Ty Atom → Type}
  {I : Type} {spec : OracleSpec.{0, 0} I}

/-- Non-stateful counterpart of the query-cost bound for a program runner. -/
theorem Program.run_queryCost_plain (P : Primitives base Op) (weight : I → Nat)
    (H : Handler base Cmd spec)
    (hhandler : ∀ {a b} (cmd : Cmd a b) (arg : a.Value base) out n,
      QueryCost weight (H cmd arg) out n → n ≤ out.steps + 1)
    {Γ a} (code : Program Op Cmd Γ a) (env : Env base Γ)
    (out : Run (a.Value base)) (n : Nat)
    (h : QueryCost weight (code.run P H env) out n) : n ≤ out.steps := by
  have hmap : QueryCost weight ((withUnitState (code.run P H env)).run ()) (out, ()) n := by
    change QueryCost weight ((fun r => (r, ())) <$> code.run P H env) (out, ()) n
    exact (QueryCost.map_iff _ _ _ _ _).2 ⟨out, h, rfl⟩
  rw [code.run_mmap withUnitState P H env] at hmap
  exact code.run_queryCost P weight (fun cmd arg => withUnitState (H cmd arg)) (by
    intro a b cmd arg state result count hc
    change QueryCost weight ((fun r => (r, state)) <$> H cmd arg) result count at hc
    obtain ⟨r, hr, rfl⟩ := (QueryCost.map_iff _ _ _ _ _).1 hc
    exact hhandler cmd arg r count hr) env () (out, ()) n hmap

variable {K : Type} [Fintype K]

/-- A conservative total-call bound from the source's uniform pricing contract.
It includes local time, so it needs no separate exact query-count extraction. -/
theorem SourceBudget.totalQueryBound (P : Primitives base Op)
    (contract : ReplyContract base Cmd) (kind : {a b : Ty Atom} → Cmd a b → K)
    {Γ a} (code : Program Op Cmd Γ a) (env : Env base Γ)
    (localTime : Nat) (queries : K → Nat)
    (hsource : SourceBudget P contract kind code env localTime queries) :
    IsTotalQueryBound
      (code.denote P (fun cmd arg => Run.value <$> pricedRequests contract (fun _ => 1) cmd arg) env)
      (localTime + ∑ k, queries k) := by
  classical
  let : ∀ q, Nonempty ((requestSpec contract).Range q) := fun q =>
    ⟨⟨(contract.responds q.instruction q.argument).choose,
      (contract.responds q.instruction q.argument).choose_spec⟩⟩
  have hcost : ∀ out n,
      QueryCost (fun _ => 1) (code.run P (pricedRequests contract (fun _ => 1)) env) out n →
      n ≤ localTime + ∑ k, queries k := by
    intro out n hn
    have hn' := code.run_queryCost_plain P (fun _ => 1)
      (pricedRequests contract (fun _ => 1)) (by
        intro a b cmd arg result count hc
        change QueryCost (fun _ => 1)
          (OracleComp.queryBind (spec := requestSpec contract) ⟨a, b, cmd, arg⟩
            (fun reply => pure (Run.mk reply.val 1))) result count at hc
        cases hc with
        | queryBind _ _ reply tail => cases tail; omega) env out n hn
    have hb := hsource (fun _ => 1) out hn.mem_support
    simp only [Nat.mul_one] at hb
    exact hn'.trans hb
  have hb := QueryCost.isQueryBound (fun _ => 1)
    (code.run P (pricedRequests contract (fun _ => 1)) env) (localTime + ∑ k, queries k) hcost
  have htotal : IsTotalQueryBound
      (code.run P (pricedRequests contract (fun _ => 1)) env) (localTime + ∑ k, queries k) := by
    simpa only [IsTotalQueryBound, Nat.succ_le_iff] using hb
  exact (isQueryBound_iff_of_map_eq (code.run_erase P _ env) _ _).1 htotal

/-- Substitute stateful semantic handlers into an unrestricted source contract.
The resulting whole-program bound is derived from source resources and the
per-command query allowance, with no bound assumed for the whole interpreter. -/
theorem SourceBudget.denote_totalQueryBound {S : Type} (P : Primitives base Op)
    (contract : ReplyContract base Cmd) (kind : {a b : Ty Atom} → Cmd a b → K)
    (hall : ∀ {a b} (cmd : Cmd a b) (arg : a.Value base) reply,
      contract.allows cmd arg reply)
    {Γ a} (code : Program Op Cmd Γ a) (env : Env base Γ)
    (localTime : Nat) (queries : K → Nat)
    (hsource : SourceBudget P contract kind code env localTime queries)
    (H : SemanticsM base Cmd (StateT S (OracleComp spec))) (step : Nat)
    (hstep : ∀ {a b} (cmd : Cmd a b) (arg : a.Value base) state,
      IsTotalQueryBound ((H cmd arg).run state) step) (state : S) :
    IsTotalQueryBound ((code.denote P H env).run state)
      ((localTime + ∑ k, queries k) * step) := by
  let impl : QueryImpl (requestSpec contract) (StateT S (OracleComp spec)) := fun q s =>
    (fun out => (⟨out.1, hall q.instruction q.argument out.1⟩, out.2)) <$>
      (H q.instruction q.argument).run s
  let source := code.denote P
    (fun cmd arg => Run.value <$> pricedRequests contract (fun _ => 1) cmd arg) env
  have he : simulateQ impl source = code.denote P H env := by
    rw [show source = _ from rfl, code.denote_simulate]
    congr 1
    funext a b cmd arg s
    simp only [pricedRequests, bind_pure_comp, Functor.map_map, simulateQ_map]
    rw [simulateQ_spec_query (spec := requestSpec contract)]
    change ((fun v : {y : b.Value base // contract.allows cmd arg y} => v.val) <$>
      impl ⟨a, b, cmd, arg⟩).run s = (H cmd arg).run s
    rw [StateT.run_map]
    change (fun out : {y : b.Value base // contract.allows cmd arg y} × S => (out.1.val, out.2)) <$>
      ((fun out : b.Value base × S => (⟨out.1, hall cmd arg out.1⟩, out.2)) <$>
        (H cmd arg).run s) = _
    simp only [Functor.map_map]
    change id <$> (H cmd arg).run s = (H cmd arg).run s
    exact id_map _
  have hsrc := hsource.totalQueryBound P contract kind code env localTime queries
  have hb : IsTotalQueryBound ((simulateQ impl source).run state)
      ((localTime + ∑ k, queries k) * step) := by
    apply IsQueryBound.simulateQ_run_of_step
      (mapBudget := fun n => n * step) (stepBudget := fun _ _ => step)
      (combine := Nat.add) hsrc
    · intro _ _ _ _ _ _ hfirst hnext
      exact isTotalQueryBound_bind hfirst hnext
    · intro q _ s _
      exact (isQueryBound_map_iff _ _ _ _ _).2 (hstep q.instruction q.argument s)
    · intro _ n hn
      change step + (n - 1) * step = n * step
      rw [Nat.sub_one_mul]
      have hh : step ≤ n * step := Nat.le_mul_of_pos_left step hn
      omega
  simpa only [he] using hb

end Signatures.Runtime
