import Proofs.Runtime.BackendProgram

/-! State-passing simulation of actual backend code. The transformation replaces
each query by a finite implemented handler, retaining the state through every
control constructor. Local functions remain the original backend realizers.
No source-language implementation or enumeration of query positions is needed. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.BackendProgram.StateSimulation

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QD : Q.IsDistributive]
  {I J S : Type} {source : OracleSpec I} {target : OracleSpec J}
  {src : Interface (C := C) source} {dst : Interface (C := C) target}

/-- Exchange a retained local value and the mutable simulator state. -/
def shuffle {A E T : Type} (a : C.Str A) (e : C.Str E) (t : C.Str T) :
    Q.Realizer (StepClass.HasProd.prod (StepClass.HasProd.prod a e) t)
      (StepClass.HasProd.prod (StepClass.HasProd.prod a t) e)
      (fun p => ((p.1.1, p.2), p.1.2)) :=
  QP.pair (QP.pair (Q.compose (QP.fst _ _) (QP.fst _ _)) (QP.snd _ _))
    (Q.compose (QP.fst _ _) (QP.snd _ _))

def associate {A E T : Type} (a : C.Str A) (e : C.Str E) (t : C.Str T) :
    Q.Realizer (StepClass.HasProd.prod (StepClass.HasProd.prod a e) t)
      (StepClass.HasProd.prod a (StepClass.HasProd.prod e t))
      (fun p => (p.1.1, (p.1.2, p.2))) :=
  QP.pair (Q.compose (QP.fst _ _) (QP.fst _ _))
    (QP.pair (Q.compose (QP.fst _ _) (QP.snd _ _)) (QP.snd _ _))

variable (store : C.Str S)
  (handler : Code Q target dst (StepClass.HasProd.prod src.position store)
    (StepClass.HasProd.prod src.response store))

def compile {A B : Type} {a : C.Str A} {b : C.Str B} : Code Q source src a b →
    Code Q target dst (StepClass.HasProd.prod a store) (StepClass.HasProd.prod b store)
  | .atomic code => .first store (.atomic code)
  | .query => handler
  | .seq initial following => .seq (compile initial) (compile following)
  | .branch (a := a) (b := b) left right =>
      .seq (.atomic (QD.distribute a b store)) (.branch (compile left) (compile right))
  | .first (a := a) (b := b) saved body =>
      .seq (.atomic (shuffle a saved store))
        (.seq (.first saved (compile body)) (.atomic (shuffle b store saved)))
  | .loop (s := s) (b := b) body stop fuel =>
      .loop (.seq (compile body) (.atomic (QD.distribute b s store))) (compile stop) fuel
  | .iterate (s := s) counter body =>
      .seq (.atomic (associate counter s store)) (.iterate counter (compile body))

variable (H : QueryImpl source (StateT S (OracleComp target)))

theorem simulate_repeat {A : Type} (body : A → OracleComp source A) (count : Nat)
    (input : A) (saved : S) :
    (simulateQ H (repeatDenote body count input)).run saved =
      repeatDenote (fun p : A × S => (simulateQ H (body p.1)).run p.2) count (input, saved) := by
  induction count generalizing input saved with
  | zero => rfl
  | succ count ih =>
      simp only [repeatDenote, simulateQ_bind, StateT.run_bind]
      congr 1
      funext p
      exact ih p.1 p.2

theorem simulate_loop {A B : Type} (body : A → OracleComp source (B ⊕ A))
    (stop : A → OracleComp source B) (fuel : Nat) (input : A) (saved : S) :
    (simulateQ H (loopDenote body stop fuel input)).run saved =
      loopDenote (fun p : A × S =>
        (fun q => Sum.elim (fun b => Sum.inl (b, q.2)) (fun a => Sum.inr (a, q.2)) q.1) <$>
          (simulateQ H (body p.1)).run p.2)
        (fun p => (simulateQ H (stop p.1)).run p.2) fuel (input, saved) := by
  induction fuel generalizing input saved with
  | zero => rfl
  | succ fuel ih =>
      simp only [loopDenote, simulateQ_bind, StateT.run_bind, bind_map_left]
      congr 1
      funext p
      cases p.1 with
      | inl result => rfl
      | inr next => exact ih next p.2

theorem compile_denote
    (hhandler : ∀ i saved, handler.denote (i, saved) =
      (fun p => (Sigma.mk i p.1, p.2)) <$> (H i).run saved)
    {A B : Type} {a : C.Str A} {b : C.Str B} (program : Code Q source src a b)
    (input : A) (saved : S) :
    (compile store handler program).denote (input, saved) =
      (simulateQ H (program.denote input)).run saved := by
  induction program generalizing saved with
  | atomic code => rfl
  | query =>
      simpa only [compile, Code.denote, simulateQ_map, simulateQ_spec_query, StateT.run_map]
        using hhandler input saved
  | seq initial following hi hf =>
      simp only [compile, Code.denote, hi, simulateQ_bind, StateT.run_bind]
      congr 1
      funext p
      exact hf p.1 p.2
  | branch left right hl hr =>
      cases input <;> simp [compile, Code.denote, hl, hr]
  | first retained body ih =>
      simp only [compile, Code.denote, pure_bind, bind_pure_comp, ih,
        Functor.map_map, simulateQ_map, StateT.run_map]
  | loop body stop fuel hb hs =>
      rw [Code.denote, simulate_loop]
      simp only [compile, Code.denote, bind_pure_comp]
      congr 1 <;> funext p
      · rw [hb]
      · exact hs p.1 p.2
  | iterate counter body ih =>
      rw [Code.denote, simulate_repeat]
      simp only [compile, Code.denote, pure_bind]
      congr 1
      funext p
      exact ih p.1 p.2

end Signatures.Runtime.BackendProgram.StateSimulation
