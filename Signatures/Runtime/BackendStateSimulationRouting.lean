import Signatures.Runtime.BackendStateSimulationExecution
import Signatures.Runtime.BackendLanguageBudget

/-! The state-passing compiler's extra local work is bounded from primitive
backend laws and encoded sizes. These bounds do not charge the original local
computation again and do not assume a budget for a compiled sampler. -/

open PFunctor

namespace Signatures.Runtime.BackendProgram.StateSimulation

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum] [QD : Q.IsDistributive]
  {S : Type} (store : C.Str S) (control : ControlCosts)
  {header : Nat} (sizes : SizeLaws Q header)
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead) (mono : Monotone overhead)
  (routing : RoutingCostLaws control overhead)

include sizes laws mono

omit QD in
theorem associate_cost {A E T : Type} (a : C.Str A) (e : C.Str E) (t : C.Str T)
    (x : A) (y : E) (z : T) (width : Nat) (hh : header ≤ width)
    (hx : Q.size a x ≤ width) (hy : Q.size e y ≤ width) (hz : Q.size t z ≤ width) :
    Q.cost (associate (Q := Q) a e t) ((x, y), z) ≤ 9 * overhead (64 * width) := by
  let bound : LocalBound (associate (Q := Q) a e t) :=
    LocalBound.pair laws (LocalBound.compose laws (LocalBound.fst laws _ _) (LocalBound.fst laws _ _))
      (LocalBound.pair laws (LocalBound.compose laws (LocalBound.fst laws _ _) (LocalBound.snd laws _ _))
        (LocalBound.snd laws _ _))
  refine (bound.cost_le ((x, y), z)).trans ?_
  have hp := @sizes.prod_le
  have hf : ∀ n ≤ 64 * width, overhead n ≤ overhead (64 * width) := fun _ h => mono h
  dsimp only [bound, LocalBound.pair, LocalBound.compose, LocalBound.fst, LocalBound.snd]
  grind only

include routing

omit QD [C.HasProd] [C.HasSum] [C.HasOption] [Q.HasCategory] QP QS sizes laws in
theorem atomic_work {A B : Type} {a : C.Str A} {b : C.Str B} {f : A → B}
    (code : Q.Realizer a b f) (input : A) (saved : S) (width : Nat)
    (hi : Q.size a input ≤ width) (ho : Q.size b (f input) ≤ width)
    (hs : Q.size store saved ≤ width) :
    localWork control code input + control.retain (Q.size store saved) (Q.size b (f input)) ≤
      Q.cost code input + 2 * overhead (64 * width) := by
  have hc := (routing.localCall _ _).trans (mono (show Q.size a input + Q.size b (f input) ≤ 64 * width by omega))
  have hr := (routing.retain _ _).trans (mono (show Q.size store saved + Q.size b (f input) ≤ 64 * width by omega))
  dsimp only [localWork]
  omega

omit QD [Q.HasCategory] QP QS laws in
theorem sequence_work {A B : Type} (a : C.Str A) (b : C.Str B)
    (input : A × S) (output : B × S) (width : Nat) (hh : header ≤ width)
    (hi : Q.size a input.1 ≤ width) (hs : Q.size store input.2 ≤ width)
    (ho : Q.size b output.1 ≤ width) (ht : Q.size store output.2 ≤ width) :
    control.sequence (Q.size (StepClass.HasProd.prod a store) input)
      (Q.size (StepClass.HasProd.prod b store) output) ≤ overhead (64 * width) := by
  have hin := sizes.prod_le a store input
  have hout := sizes.prod_le b store output
  exact (routing.sequence _ _).trans (mono (by omega))

omit QD in
theorem first_work {A B T : Type} (a : C.Str A) (b : C.Str B) (retained : C.Str T)
    (input : A × T) (saved : S) (output : B × S) (width : Nat) (hh : header ≤ width)
    (hi : Q.size a input.1 ≤ width) (hk : Q.size retained input.2 ≤ width)
    (hs : Q.size store saved ≤ width) (ho : Q.size b output.1 ≤ width)
    (ht : Q.size store output.2 ≤ width) :
    firstWork (Q := Q) store control a b retained input saved output ≤ 23 * overhead (64 * width) := by
  have hin := Language.contextReturn_cost_of_width sizes laws mono a store retained
    input.1 input.2 saved width hh hi hk hs
  have hout := Language.contextReturn_cost_of_width sizes laws mono b retained store
    output.1 output.2 input.2 width hh ho ht hk
  change Q.cost (shuffle (Q := Q) a retained store) ((input.1, input.2), saved) ≤ _ at hin
  change Q.cost (shuffle (Q := Q) b store retained) ((output.1, output.2), input.2) ≤ _ at hout
  have hf : ∀ n ≤ 64 * width, overhead n ≤ overhead (64 * width) := fun _ h => mono h
  have hm := hf (32 * width) (by omega)
  have hp := @sizes.prod_le
  have hc := routing.localCall
  have hj := routing.sequence
  have hr := routing.retain
  rcases input with ⟨input, kept⟩
  rcases output with ⟨output, next⟩
  dsimp only [firstWork, localWork] at *
  grind only

omit QD in
theorem iteration_work {A : Type} (a : C.Str A) (counter : C.Str Nat)
    (input : (Nat × A) × S) (width : Nat) (hh : header ≤ width)
    (hn : Q.size counter input.1.1 ≤ width) (hi : Q.size a input.1.2 ≤ width)
    (hs : Q.size store input.2 ≤ width) :
    iterationWork (Q := Q) store control a counter input ≤ 11 * overhead (64 * width) := by
  have ha := associate_cost sizes laws mono counter a store input.1.1 input.1.2 input.2 width hh hn hi hs
  change Q.cost (associate (Q := Q) counter a store) input ≤ _ at ha
  have hp := @sizes.prod_le
  have hc := routing.localCall
  have hj := routing.sequence
  have hf : ∀ n ≤ 64 * width, overhead n ≤ overhead (64 * width) := fun _ h => mono h
  dsimp only [iterationWork, localWork]
  grind only

variable (distribution : ∀ {A B T : Type} (a : C.Str A) (b : C.Str B) (t : C.Str T) (p : (A ⊕ B) × T),
  Q.cost (QD.distribute a b t) p ≤ overhead
    (Q.size (StepClass.HasProd.prod (StepClass.HasSum.sum a b) t) p +
      Q.size (StepClass.HasSum.sum (StepClass.HasProd.prod a t) (StepClass.HasProd.prod b t)) (distributeValue p)))

include distribution

omit [Q.HasCategory] QP QS laws in
theorem branch_work {A B : Type} (a : C.Str A) (b : C.Str B) (input : A ⊕ B) (saved : S)
    (width : Nat) (hh : header ≤ width)
    (hi : Q.size (StepClass.HasSum.sum a b) input ≤ width) (hs : Q.size store saved ≤ width) :
    branchWork (Q := Q) store control a b input saved ≤ 4 * overhead (64 * width) := by
  have hp := sizes.prod_le (StepClass.HasSum.sum a b) store (input, saved)
  have hd := sizes.distribute_le a b store (input, saved)
  change Q.size (StepClass.HasSum.sum (StepClass.HasProd.prod a store) (StepClass.HasProd.prod b store))
    (distributeValue (input, saved)) ≤ _ at hd
  have ht := distribution a b store (input, saved)
  have hc := routing.localCall
  have hj := routing.sequence
  have hb := routing.branch
  have hf : ∀ n ≤ 64 * width, overhead n ≤ overhead (64 * width) := fun _ h => mono h
  dsimp only [branchWork, localWork, distributeValue] at *
  grind only

omit [Q.HasCategory] QP QS laws in
theorem loop_body_work {A B : Type} (a : C.Str A) (b : C.Str B)
    (input : A × S) (output : (B ⊕ A) × S) (width : Nat) (hh : header ≤ width)
    (hi : Q.size a input.1 ≤ width) (hs : Q.size store input.2 ≤ width)
    (ho : Q.size (StepClass.HasSum.sum b a) output.1 ≤ width) (ht : Q.size store output.2 ≤ width) :
    loopBodyWork (Q := Q) store control a b input output ≤ 3 * overhead (64 * width) := by
  have hp := @sizes.prod_le
  have hd := sizes.distribute_le b a store output
  change Q.size (StepClass.HasSum.sum (StepClass.HasProd.prod b store) (StepClass.HasProd.prod a store))
    (distributeValue output) ≤ _ at hd
  have hw := distribution b a store output
  have hc := routing.localCall
  have hj := routing.sequence
  have hf : ∀ n ≤ 64 * width, overhead n ≤ overhead (64 * width) := fun _ h => mono h
  dsimp only [loopBodyWork, localWork, distributeValue] at *
  grind only

end Signatures.Runtime.BackendProgram.StateSimulation
