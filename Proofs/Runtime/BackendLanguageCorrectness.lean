import Proofs.Runtime.BackendLanguage

/-! Exact semantics of the state-passing backend compiler, including adaptive
effects and preservation of the local environment across loop iterations. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.BackendProgram.Language

universe v w x

theorem repeatDenote_context {I A E S : Type} {spec : OracleSpec I}
    (step : A × E → StateT S (OracleComp spec) A)
    (count : Nat) (acc : A) (env : E) (saved : S) :
    repeatDenote (fun p : (A × E) × S =>
      (fun q => ((q.1, p.1.2), q.2)) <$> (step p.1).run p.2) count ((acc, env), saved) =
        (fun q => ((q.1, env), q.2)) <$>
          (repeatDenote (fun a => step (a, env)) count acc).run saved := by
  induction count generalizing acc saved with
  | zero =>
      change pure ((acc, env), saved) = (fun q => ((q.1, env), q.2)) <$>
        (pure (acc, saved) : OracleComp spec (A × S))
      simp
  | succ count ih =>
      simp only [repeatDenote, StateT.run_bind, bind_map_left, map_bind]
      congr 1
      funext result
      exact ih result.1 result.2

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {I S : Type} {spec : OracleSpec I} {iface : Interface (C := C) spec}
  {Atom : Type} {base : Atom → Type} {Op Cmd : Ty Atom → Ty Atom → Type}
  (rep : LanguageRepresentation C base) (data : DataCode Q rep.data)
  (P : Primitives base Op)
  (primitive : {a b : Ty Atom} → (instr : Op a b) →
    Q.Realizer (rep.ty a) (rep.ty b) (P.execute instr))
  (store : C.Str S)
  (effect : {a b : Ty Atom} → Cmd a b →
    Code Q spec iface (StepClass.HasProd.prod (rep.ty a) store)
      (StepClass.HasProd.prod (rep.ty b) store))
  (H : SemanticsM base Cmd (StateT S (OracleComp spec)))
  (heffect : ∀ {a b} (instr : Cmd a b) input saved,
    (effect instr).denote (input, saved) = (H instr input).run saved)

include heffect

theorem compile_denote {Γ a} (program : Program Op Cmd Γ a)
    (env : Env base Γ) (saved : S) :
    (compile rep data P primitive store effect program).denote (env, saved) =
      (program.denote P H env).run saved := by
  induction program generalizing saved with
  | ret expression =>
      simp [compile, Code.denote, Program.denote, StateT.run_pure]
  | query instr arg => simp [compile, Code.denote, Program.denote, heffect]
  | bind initial following hi hf =>
      simp only [compile, Code.denote, withContext_denote, hi, bind_map_left,
        Program.denote, StateT.run_bind]
      congr 1
      funext p
      exact hf _ _
  | branch cond yes no hy hn =>
      by_cases h : cond.denote P env = true <;>
        simp [compile, Code.denote, choose, Program.denote, h, hy, hn]
  | @loop Γ a count init body ih =>
      have hb : (withContext store (QP.snd (rep.ty a) (rep.env Γ))
          (compile rep data P primitive store effect body)).denote =
          fun p => (fun q => ((q.1, p.1.2), q.2)) <$> (body.denote P H p.1).run p.2 := by
        funext p
        rw [withContext_denote, ih]
      change (pure (count.denote P env, ((init.denote P env, env), saved)) >>= fun p =>
        (repeatDenote (withContext store (QP.snd (rep.ty a) (rep.env Γ))
          (compile rep data P primitive store effect body)).denote p.1 p.2 >>= fun q =>
            pure (q.1.1, q.2))) = _
      simp only [pure_bind, hb, repeatDenote_context, bind_pure_comp]
      simp [Program.denote, Functor.map_map]
  | call body args ih =>
      simp [compile, Code.denote, Program.denote, ih]

/-- The actual target program is constructed by both compilers. Backend costs
are left intact; this semantic theorem does not identify them with source steps. -/
theorem compiled_erase {control : ControlCosts} {queryCost : (i : I) → spec.Range i → Nat}
    (backend : Backend.{v, w, x} Q spec iface control queryCost)
    {Γ a} (program : Program Op Cmd Γ a) (env : Env base Γ) (saved : S) :
    Run.value <$> backend.execute
      (backend.compile (compile rep data P primitive store effect program)) (env, saved) =
        (program.denote P H env).run saved := by
  rw [backend.compile_erase]
  exact compile_denote rep data P primitive store effect H heffect program env saved

end Signatures.Runtime.BackendProgram.Language
