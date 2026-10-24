import Proofs.Runtime.Sampling

/-! Embed the compiled full-table sampler in an ambient machine store. Sampling leaves
that store unchanged, and the embedding preserves the exact charged runtime. -/

open OracleComp OracleSpec

namespace Signatures.Runtime

theorem repeatRun_run_state {m : Type → Type} [Monad m] [LawfulMonad m] {S α : Type}
    (step : α → m (Run α)) (stateStep : α → StateT S m (Run α))
    (hstep : ∀ x state, (stateStep x).run state = (fun r => (r, state)) <$> step x)
    (n : Nat) (x : α) (state : S) :
    (repeatRun stateStep n x).run state = (fun r => (r, state)) <$> repeatRun step n x := by
  induction n generalizing x with
  | zero => simp [repeatRun]
  | succ n ih =>
      simp [repeatRun, StateT.run_bind, hstep, ih, bind_map_left, map_bind, bind_pure_comp]

variable {Atom : Type} {base : Atom → Type} {Op Cmd Cmd' : Ty Atom → Ty Atom → Type}
  {cell : Ty Atom} {I S : Type} {spec : OracleSpec I}

theorem drawAndCons_run_state (P : Primitives base Op) (H : Handler base Cmd spec)
    (HS : HandlerM base Cmd' (StateT S (OracleComp spec)))
    (draw : Cmd .unit cell) (draw' : Cmd' .unit cell)
    (hdraw : ∀ state, (HS draw' ()).run state = (fun r => (r, state)) <$> H draw ())
    (xs : List (cell.Value base)) (n : Nat) (state : S) :
    ((drawAndCons draw').run P HS (xs, n, ())).run state =
      (fun r => (r, state)) <$> (drawAndCons draw).run P H (xs, n, ()) := by
  simp [drawAndCons, Program.run, Expr.run, Var.get, Var.depth, hdraw,
    bind_pure_comp]

theorem sampleList_run_state (P : Primitives base Op) (H : Handler base Cmd spec)
    (HS : HandlerM base Cmd' (StateT S (OracleComp spec)))
    (draw : Cmd .unit cell) (draw' : Cmd' .unit cell)
    (hdraw : ∀ state, (HS draw' ()).run state = (fun r => (r, state)) <$> H draw ())
    (n : Nat) (state : S) :
    ((sampleList draw').run P HS (n, ())).run state =
      (fun r => (r, state)) <$> (sampleList draw).run P H (n, ()) := by
  have hr := repeatRun_run_state
    (fun xs => (drawAndCons draw).run P H (xs, n, ()))
    (fun xs => (drawAndCons draw').run P HS (xs, n, ()))
    (fun xs state => drawAndCons_run_state P H HS draw draw' hdraw xs n state) n [] state
  simp [sampleList, Program.run, Expr.run, Var.get, Var.depth, hr, bind_pure_comp]

theorem sampleTable_run_state (P : Primitives base Op) (H : Handler base Cmd spec)
    (HS : HandlerM base Cmd' (StateT S (OracleComp spec)))
    (draw : Cmd .unit cell) (draw' : Cmd' .unit cell)
    (hdraw : ∀ state, (HS draw' ()).run state = (fun r => (r, state)) <$> H draw ())
    (n : Nat) (state : S) :
    ((sampleTable draw').run P HS (n, ())).run state =
      (fun r => (r, state)) <$> (sampleTable draw).run P H (n, ()) := by
  have hr := sampleList_run_state P H HS draw draw' hdraw n state
  simp [sampleTable, Program.run, hr, bind_pure_comp]

end Signatures.Runtime
