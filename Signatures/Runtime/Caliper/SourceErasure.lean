import Signatures.Runtime.Caliper.SourceCompilation

/-! Erasing bounded-domain witnesses recovers the existing source program and
its original oracle computation. Together with compilation correctness this is
the bridge from unchanged reduction/game semantics to actual Caliper execution.
-/

namespace Signatures.Runtime.CaliperBackend.SourceCompilation

open Caliper OracleComp OracleSpec PFunctor BoundedSource

universe v u

variable {w : Nat} {I : Type} {spec : OracleSpec I}

theorem repeat_map {S T : Type} (view : T → S) (body : S → OracleComp spec S)
    (boundedBody : T → OracleComp spec T)
    (body_eq : ∀ value, view <$> boundedBody value = body (view value)) (count : Nat) (value : T) :
    view <$> repeatDenote boundedBody count value = repeatDenote body count (view value) := by
  induction count generalizing value with
  | zero => simp [repeatDenote]
  | succ count ih =>
    simp only [repeatDenote, ← bind_pure_comp, bind_assoc]
    rw [← body_eq value, bind_map_left]
    congr 1
    funext next
    simpa only [bind_pure_comp] using ih next

theorem loop_map {S T B D : Type} (stateView : T → S) (resultView : D → B)
    (body : S → OracleComp spec (B ⊕ S)) (stop : S → OracleComp spec B)
    (boundedBody : T → OracleComp spec (D ⊕ T)) (boundedStop : T → OracleComp spec D)
    (body_eq : ∀ value, Sum.map resultView stateView <$> boundedBody value = body (stateView value))
    (stop_eq : ∀ value, resultView <$> boundedStop value = stop (stateView value))
    (fuel : Nat) (value : T) :
    resultView <$> BackendProgram.loopDenote boundedBody boundedStop fuel value =
      BackendProgram.loopDenote body stop fuel (stateView value) := by
  induction fuel generalizing value with
  | zero => exact stop_eq value
  | succ fuel ih =>
    simp only [BackendProgram.loopDenote, ← bind_pure_comp, bind_assoc]
    rw [← body_eq value, bind_map_left]
    congr 1
    funext next
    cases next with
    | inl answer => simp
    | inr state => simpa only [Sum.map_inr, bind_pure_comp] using ih state

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
    {Q : QuantitativeStepClass.{0, v, u} C} {sourceIface : BackendProgram.Interface (C := C) spec}
    {targetIface : Interface w spec} {cost : WordIO.Costs} {hw : 16 < 2 ^ w}

theorem Compilation.erase {A B : Type} {a : C.Str A} {b : C.Str B}
    {source : BackendProgram.Code Q spec sourceIface a b} {input : Layout w A} {output : Layout w B}
    (code : Compilation targetIface cost hw source input output) (value : input.Value) :
    Subtype.val <$> code.boundedDenote value = source.denote value.val := by
  induction code with
  | atomic source implementation => rfl
  | query => rfl
  | seq initial following ih₁ ih₂ =>
    simp only [Compilation.boundedDenote, BackendProgram.Code.denote, ← bind_pure_comp, bind_assoc]
    rw [← ih₁ value, bind_map_left]
    congr 1
    funext intermediate
    simpa only [bind_pure_comp] using ih₂ intermediate
  | @branch A B D a b d left right leftInput rightInput output first second fits ih₁ ih₂ =>
    rcases value with ⟨value, valid⟩
    cases value with
    | inl argument =>
      simpa [Compilation.boundedDenote, BackendProgram.Code.denote, sumView] using ih₁ ⟨argument, valid⟩
    | inr argument =>
      simpa [Compilation.boundedDenote, BackendProgram.Code.denote, sumView] using ih₂ ⟨argument, valid⟩
  | @first A B S a b s body input output saved code inputFits outputFits ih =>
    have mapped := congrArg (fun computation : OracleComp spec B =>
      (fun result => (result, value.val.2)) <$> computation) (ih (productView input saved value).1)
    calc
      _ = (fun result : output.Value => (result.val, value.val.2)) <$>
          code.boundedDenote (productView input saved value).1 := (PFunctor.FreeM.comp_map _ _ _).symm
      _ = (fun result => (result, value.val.2)) <$>
          (Subtype.val <$> code.boundedDenote (productView input saved value).1) :=
        PFunctor.FreeM.comp_map (fun result : B => (result, value.val.2))
          (Subtype.val : output.Value → B) (code.boundedDenote (productView input saved value).1)
      _ = _ := mapped
  | @loop S B s b body stop state result fits step finish fuel ihBody ihStop =>
    apply loop_map Subtype.val Subtype.val body.denote stop.denote
      (fun value => sumView result state <$> step.boundedDenote value) finish.boundedDenote _ ihStop fuel value
    intro value
    have shape (next : (result.sum state (width_pos hw) fits).Value) :
        Sum.map Subtype.val Subtype.val (sumView result state next) = next.val := by
      rcases next with ⟨next, valid⟩
      cases next <;> rfl
    have composed : (fun next : (result.sum state (width_pos hw) fits).Value =>
        Sum.map Subtype.val Subtype.val (sumView result state next)) = Subtype.val := funext shape
    calc
      _ = (fun next => Sum.map Subtype.val Subtype.val (sumView result state next)) <$>
          step.boundedDenote value := (PFunctor.FreeM.comp_map _ _ _).symm
      _ = Subtype.val <$> step.boundedDenote value := congrArg (fun f => f <$> step.boundedDenote value) composed
      _ = _ := ihBody value
  | iterate counter code fuel counterFits storageFits ih =>
    exact repeat_map Subtype.val _ code.boundedDenote ih value.val.1 ⟨value.val.2, value.property.2⟩

/-- The final observation is the original reduction-language computation, with
all capacity witnesses erased. The machine program and execution profile are
those constructed recursively by `compile`. -/
theorem Compilation.observe {A B : Type} {a : C.Str A} {b : C.Str B}
    {source : BackendProgram.Code Q spec sourceIface a b} {input : Layout w A} {output : Layout w B}
    (code : Compilation targetIface cost hw source input output) (allocation : 1 ≤ cost.machine.allocPerWord)
    (tape : RandomTape w) (value : input.Value) (before : State w)
    (represented : input.representation.Holds value before) :
    (fun result => Subtype.val <$> Interactive.observe output.representation result) <$>
      code.compile.execute targetIface.port cost tape before = some <$> source.denote value.val := by
  have observed := (code.correct allocation).observe tape value before represented
  have mapped := congrArg (fun computation : OracleComp spec (Option output.Value) =>
    (fun result => Subtype.val <$> result) <$> computation) observed
  have erased := congrArg (fun computation : OracleComp spec B => some <$> computation) (code.erase value)
  have middle : (fun result => Subtype.val <$> result) <$> some <$> code.boundedDenote value =
      some <$> Subtype.val <$> code.boundedDenote value :=
    (PFunctor.FreeM.comp_map _ _ _).symm.trans
      (PFunctor.FreeM.comp_map (some : B → Option B) (Subtype.val : output.Value → B) (code.boundedDenote value))
  exact (PFunctor.FreeM.comp_map _ _ _).trans (mapped.trans (middle.trans erased))

end Signatures.Runtime.CaliperBackend.SourceCompilation
