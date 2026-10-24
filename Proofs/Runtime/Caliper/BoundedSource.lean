import Proofs.Runtime.Caliper.Loop

/-! Bounded representations of the existing, unbounded source types.

The mathematical source remains `Nat`, `List A`, and ordinary products/sums.
A layout represents the subtype admitted by its capacity invariant. Local
implementations prove preservation of that invariant and contain actual Caliper
code. This avoids claiming universal fixed-width encodings for unbounded types.
-/

namespace Signatures.Runtime.CaliperBackend

open Caliper

variable {w : Nat} {A B D : Type}

/-- Relabeling changes only the mathematical view of the same stored words.
It is not an executable conversion or an instruction. -/
def Encoding.transport (encoding : Encoding w B) (view : A ≃ B) : Encoding w A where
  words := encoding.words
  encode value := encoding.encode (view value)
  decode bytes := view.symm <$> encoding.decode bytes
  encode_length value := encoding.encode_length (view value)
  decode_encode value := by simp [encoding.decode_encode]
  decode_length bytes value decoded := by
    cases h : encoding.decode bytes with
    | none => simp [h] at decoded
    | some output => exact encoding.decode_length bytes output h

def Representation.transport (representation : Representation w B) (view : A ≃ B) : Representation w A :=
  ⟨representation.encoding.transport view, representation.fits⟩

def Realizer.transport {cost : CostModel} {A' B' : Type}
    {input : Representation w A} {output : Representation w B} {f : A → B}
    (body : Realizer cost input output f) (inputView : A' ≃ A) (outputView : B' ≃ B) :
    Realizer cost (input.transport inputView) (output.transport outputView)
      (fun value => outputView.symm (f (inputView value))) where
  code := body.code
  positive_width := body.positive_width
  description_fits := body.description_fits
  random_free := body.random_free
  time value := body.time (inputView value)
  net value := body.net (inputView value)
  workspace value := body.workspace (inputView value)
  correct tape value before represented := by
    obtain ⟨after, net, peak, execution, result, hn, hp⟩ :=
      body.correct tape (inputView value) before represented
    refine ⟨after, net, peak, execution, ?_, hn, hp⟩
    simpa [Representation.Holds, Representation.transport, Encoding.transport] using result

/-- A proved equality of encodings permits a different specification of the
same output bytes. No new instructions or free data conversion are introduced. -/
def Realizer.viewOutput {cost : CostModel} {B' : Type}
    {input : Representation w A} {output : Representation w B} {f : A → B}
    (body : Realizer cost input output f) (target : Representation w B') (g : A → B')
    (sameBytes : ∀ value, target.encoding.encode (g value) = output.encoding.encode (f value)) :
    Realizer cost input target g where
  code := body.code
  positive_width := body.positive_width
  description_fits := body.description_fits
  random_free := body.random_free
  time := body.time
  net := body.net
  workspace := body.workspace
  correct tape value before represented := by
    obtain ⟨after, net, peak, execution, result, hn, hp⟩ := body.correct tape value before represented
    exact ⟨after, net, peak, execution,
      ⟨result.1, result.2.1.trans (sameBytes value).symm, result.2.2⟩, hn, hp⟩

namespace BoundedSource

structure Layout (w : Nat) (A : Type) where
  valid : A → Prop
  representation : Representation w {value : A // valid value}

abbrev Layout.Value (layout : Layout w A) := {value : A // layout.valid value}

def Layout.all (representation : Representation w A) : Layout w A where
  valid _ := True
  representation := representation.transport
    { toFun := Subtype.val
      invFun := fun value => ⟨value, trivial⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

def Layout.counter (w bound : Nat) (hw : 0 < w) (fits : bound ≤ 2 ^ w) : Layout w Nat where
  valid value := value < bound
  representation := (Representation.fin w bound hw fits).transport
    { toFun := fun value => ⟨value.val, value.property⟩
      invFun := fun value => ⟨value.val, value.isLt⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

def Layout.list (entry : Representation w A) (capacity : Nat)
    (count_fits : capacity < 2 ^ w) (storage_fits : 1 + capacity * entry.encoding.words < 2 ^ w) :
    Layout w (List A) where
  valid values := values.length ≤ capacity
  representation := entry.boundedList capacity count_fits storage_fits

def productView (left : Layout w A) (right : Layout w B) :
    {value : A × B // left.valid value.1 ∧ right.valid value.2} ≃ (left.Value × right.Value) where
  toFun value := (⟨value.val.1, value.property.1⟩, ⟨value.val.2, value.property.2⟩)
  invFun value := ⟨(value.1.val, value.2.val), value.1.property, value.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def Layout.prod (left : Layout w A) (right : Layout w B)
    (fits : left.representation.encoding.words + right.representation.encoding.words < 2 ^ w) :
    Layout w (A × B) where
  valid value := left.valid value.1 ∧ right.valid value.2
  representation := (left.representation.prod right.representation fits).transport (productView left right)

def sumView (left : Layout w A) (right : Layout w B) :
    {value : A ⊕ B // Sum.elim left.valid right.valid value} ≃ (left.Value ⊕ right.Value) where
  toFun value := match value with
    | ⟨.inl x, valid⟩ => .inl ⟨x, valid⟩
    | ⟨.inr x, valid⟩ => .inr ⟨x, valid⟩
  invFun value := match value with
    | .inl x => ⟨.inl x.val, x.property⟩
    | .inr x => ⟨.inr x.val, x.property⟩
  left_inv value := by rcases value with ⟨value, valid⟩; cases value <;> rfl
  right_inv value := by cases value <;> rfl

def Layout.sum (left : Layout w A) (right : Layout w B) (hw : 0 < w)
    (fits : 1 + max left.representation.encoding.words right.representation.encoding.words < 2 ^ w) :
    Layout w (A ⊕ B) where
  valid := Sum.elim left.valid right.valid
  representation := (left.representation.sum right.representation hw fits).transport (sumView left right)

/-- A local source function is implemented on its admitted domain, with output
capacity proved preserved. Its behavior outside that domain is not assumed. -/
structure Implementation (cost : CostModel) (input : Layout w A) (output : Layout w B) (f : A → B) where
  preserves : ∀ value, input.valid value → output.valid (f value)
  program : Realizer cost input.representation output.representation
    (fun value => ⟨f value.val, preserves value.val value.property⟩)

variable {cost : CostModel} {input : Layout w A} {middle : Layout w B} {output : Layout w D}
  {f : A → B} {g : B → D}

def Implementation.identity (input : Layout w A) (hw : 0 < w) : Implementation cost input input id where
  preserves _ := id
  program := Realizer.identity hw input.representation

def Implementation.then (first : Implementation cost input middle f)
    (second : Implementation cost middle output g) : Implementation cost input output (g ∘ f) where
  preserves value valid := second.preserves (f value) (first.preserves value valid)
  program := first.program.then second.program

/-- The source output is obtained from an actual target execution. All input
and output words and the full execution profile are retained in the conclusion. -/
theorem Implementation.exec (implementation : Implementation cost input middle f)
    (tape : RandomTape w) (value : A) (valid : input.valid value) (before : State w)
    (represented : input.representation.Holds ⟨value, valid⟩ before) :
    ∃ after net peak, Caliper.Exec cost tape implementation.program.code before after
      (implementation.program.time ⟨value, valid⟩) net peak ∧
      middle.representation.Holds ⟨f value, implementation.preserves value valid⟩ after ∧
      net ≤ implementation.program.net ⟨value, valid⟩ ∧
      peak ≤ implementation.program.workspace ⟨value, valid⟩ :=
  implementation.program.correct tape ⟨value, valid⟩ before represented

/-- The bounded and unbounded mathematical views have identical loop behavior
provided each body step preserves the state/result domain. This is the invariant
needed to use finite machine layouts for the original source loop. -/
theorem loop_preserves (state : Layout w A) (result : Layout w B)
    (body : A → B ⊕ A) (stop : A → B)
    (body_valid : ∀ value, state.valid value → Sum.elim result.valid state.valid (body value))
    (stop_valid : ∀ value, state.valid value → result.valid (stop value))
    (fuel : Nat) (value : A) (valid : state.valid value) :
    result.valid (loopFunction body stop fuel value) := by
  induction fuel generalizing value with
  | zero => exact stop_valid value valid
  | succ fuel ih =>
    have next := body_valid value valid
    cases h : body value with
    | inl output => simpa [loopFunction, h] using next
    | inr nextState => simpa [loopFunction, h] using (ih nextState (by simpa [h] using next))

def liftedBody (state : Layout w A) (result : Layout w B) (body : A → B ⊕ A)
    (preserves : ∀ value, state.valid value → Sum.elim result.valid state.valid (body value)) :
    state.Value → result.Value ⊕ state.Value :=
  fun value => sumView result state ⟨body value.val, preserves value.val value.property⟩

theorem liftedLoop_value (state : Layout w A) (result : Layout w B)
    (body : A → B ⊕ A) (stop : A → B)
    (body_valid : ∀ value, state.valid value → Sum.elim result.valid state.valid (body value))
    (stop_valid : ∀ value, state.valid value → result.valid (stop value))
    (fuel : Nat) (value : state.Value) :
    (loopFunction (liftedBody state result body body_valid)
      (fun x => ⟨stop x.val, stop_valid x.val x.property⟩) fuel value).val =
        loopFunction body stop fuel value.val := by
  induction fuel generalizing value with
  | zero => rfl
  | succ fuel ih =>
    have step : ∀ next : {value : B ⊕ A // Sum.elim result.valid state.valid value},
        (Sum.elim id (loopFunction (liftedBody state result body body_valid)
          (fun x => ⟨stop x.val, stop_valid x.val x.property⟩) fuel) (sumView result state next)).val =
        Sum.elim id (loopFunction body stop fuel) next.val := by
      rintro ⟨next, valid⟩
      cases next with
      | inl answer => rfl
      | inr nextState => exact ih ⟨nextState, valid⟩
    exact step ⟨body value.val, body_valid value.val value.property⟩

/-- Compile the original source loop on its reachable domain. The only local
implementation obligations are for its body and exhaustion routine. -/
def Implementation.loop (allocation : 1 ≤ cost.allocPerWord)
    (state : Layout w A) (result : Layout w B) (hw : 16 < 2 ^ w)
    (fits : 1 + max result.representation.encoding.words state.representation.encoding.words < 2 ^ w)
    {body : A → B ⊕ A} {stop : A → B}
    (step : Implementation cost state (result.sum state (width_pos hw) fits) body)
    (finish : Implementation cost state result stop) (fuel : Nat) :
    Implementation cost state result (loopFunction body stop fuel) where
  preserves := loop_preserves state result body stop step.preserves finish.preserves fuel
  program :=
    let lifted := step.program.viewOutput
      (result.representation.sum state.representation (width_pos hw) fits)
      (liftedBody state result body step.preserves) (fun _ => rfl)
    (loopRealizer cost allocation state.representation result.representation hw fits
      lifted finish.program fuel).viewOutput result.representation
      (fun value => ⟨loopFunction body stop fuel value.val,
        loop_preserves state result body stop step.preserves finish.preserves fuel value.val value.property⟩)
      (fun value => congrArg result.representation.encoding.encode
        (Subtype.ext (liftedLoop_value state result body stop step.preserves finish.preserves fuel value).symm))

end BoundedSource
end Signatures.Runtime.CaliperBackend
