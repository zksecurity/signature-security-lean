import Signatures.Runtime.Caliper.InteractiveControlBounds
import Signatures.Runtime.Caliper.RestrictedLayout

/-! Refinement on reachable domains. A finite buffer need only have room for the
remaining calls. These predicates are proof invariants, not unchecked runtime
tests or additional instructions. All state changes still execute the same
Caliper program as the unconditional control constructors. -/

namespace Signatures.Runtime.CaliperBackend

open Caliper OracleComp OracleSpec

variable {w : Nat} {I A B D : Type} {spec : OracleSpec I}

/-- Keep reachability when composing structural refinement. The continuation
may rely on an invariant proved for every supported source answer. -/
theorem Synchronizes.with_support {relation : A → B → Prop}
    {left : OracleComp spec A} {right : OracleComp spec B}
    (related : Synchronizes relation left right) :
    Synchronizes (fun a b => relation a b ∧ a ∈ support left ∧ b ∈ support right) left right := by
  induction related with
  | pure h => exact .pure ⟨h, by simp, by simp⟩
  | query position _ ih =>
    exact .query position fun answer => (ih answer).mono fun _ _ h =>
      ⟨h.1, Set.mem_iUnion.mpr ⟨answer, h.2.1⟩, Set.mem_iUnion.mpr ⟨answer, h.2.2⟩⟩

namespace Interactive

variable {port : Port w spec} {cost : WordIO.Costs}

def RefinesOn (predicate : A → Prop) (port : Port w spec) (cost : WordIO.Costs)
    (input : Representation w A) (output : Representation w B)
    (source : A → OracleComp spec B) (target : Code w) : Prop :=
  ∀ tape value, predicate value → ∀ before, input.Holds value before →
    Synchronizes (Represents output cost tape (target.lower port) before)
      (source value) (target.execute port cost tape before)

theorem Refines.on {input : Representation w A} {output : Representation w B}
    {source : A → OracleComp spec B} {target : Code w}
    (refined : Refines port cost input output source target) (predicate : A → Prop) :
    RefinesOn predicate port cost input output source target :=
  fun tape value _ before holds => refined tape value before holds

theorem RefinesOn.restrict {predicate : A → Prop} [DecidablePred predicate]
    {input : Representation w A} {output : Representation w B}
    {source : A → OracleComp spec B} {target : Code w}
    (refined : RefinesOn predicate port cost input output source target) :
    Refines port cost (input.restrict predicate) output (fun value => source value.val) target :=
  fun tape value before holds => refined tape value.val value.property before holds

theorem RefinesOn.observe {predicate : A → Prop}
    {input : Representation w A} {output : Representation w B}
    {source : A → OracleComp spec B} {target : Code w}
    (refined : RefinesOn predicate port cost input output source target)
    (tape : RandomTape w) (value : A) (valid : predicate value) (before : State w)
    (represented : input.Holds value before) :
    Interactive.observe output <$> target.execute port cost tape before = some <$> source value :=
  ((refined tape value valid before represented).map_eq some (Interactive.observe output)
    (fun _ _ h => h.observe.symm)).symm

theorem RefinesOn.seq {p : A → Prop} {q : B → Prop}
    {input : Representation w A} {middle : Representation w B} {output : Representation w D}
    {f : A → OracleComp spec B} {g : B → OracleComp spec D} {first second : Code w}
    (firstRefines : RefinesOn p port cost input middle f first)
    (secondRefines : RefinesOn q port cost middle output g second)
    (preserves : ∀ value, p value → ∀ answer ∈ support (f value), q answer) :
    RefinesOn p port cost input output (fun value => f value >>= g) (.seq first second) := by
  intro tape value valid before represented
  apply (firstRefines tape value valid before represented).with_support.bind g
    (fun result => match result with
      | none => pure none
      | some left => (fun right => join left <$> right) <$> second.execute port cost tape left.state)
  intro intermediate result related
  obtain ⟨left, rfl, holds, _, leftExec⟩ := related.1
  have next := secondRefines tape intermediate (preserves value valid intermediate related.2.1) left.state holds
  simpa using next.map id (fun result => join left <$> result) (by
    intro value result related
    obtain ⟨right, rfl, holds, remaining, rightExec⟩ := related
    exact ⟨join left right, rfl, holds, remaining, .seq leftExec rightExec⟩)

theorem RefinesOn.dispatch (left : Representation w A) (right : Representation w B) (output : Representation w D)
    {p : A → Prop} {q : B → Prop}
    {f : A → OracleComp spec D} {g : B → OracleComp spec D} {leftBody rightBody : Code w}
    (leftRefines : RefinesOn p port cost left output f leftBody)
    (rightRefines : RefinesOn q port cost right output g rightBody)
    (hw : 0 < w) (fits : 1 + max left.encoding.words right.encoding.words < 2 ^ w) :
    RefinesOn (Sum.elim p q) port cost (left.sum right hw fits) output (Sum.elim f g)
      (dispatch leftBody rightBody left.encoding.words right.encoding.words) := by
  classical
  have refined := Refines.dispatch (left.restrict p) (right.restrict q) output
    leftRefines.restrict rightRefines.restrict hw fits
  intro tape value valid before represented
  cases value with
  | inl value => exact refined tape (.inl ⟨value, valid⟩) before represented
  | inr value => exact refined tape (.inr ⟨value, valid⟩) before represented

theorem RefinesOn.retain {S : Type} {predicate : A → Prop}
    {input : Representation w A} {output : Representation w B}
    {source : A → OracleComp spec B} {body : Code w}
    (refined : RefinesOn predicate port cost input output source body)
    (allocation : 1 ≤ cost.machine.allocPerWord) (saved : Representation w S)
    (hw : 16 < 2 ^ w) (inputFits : input.encoding.words + saved.encoding.words < 2 ^ w)
    (outputFits : output.encoding.words + saved.encoding.words < 2 ^ w) :
    RefinesOn (fun value => predicate value.1) port cost
      (input.prod saved inputFits) (output.prod saved outputFits)
      (fun value => (fun answer => (answer, value.2)) <$> source value.1)
      (Interactive.retain body (savedBuffer port body) input.encoding.words output.encoding.words saved.encoding.words) := by
  classical
  intro tape value valid before holds
  exact (refined.restrict.retain allocation saved hw inputFits outputFits)
    tape (⟨value.1, valid⟩, value.2) before holds

/-- The same executed loop is valid with decreasing reserve. In particular,
correctness need not assume that a full finite cache can answer another miss. -/
theorem RefinesOn.loop (state : Representation w A) (result : Representation w B)
    (invariant : Nat → A → Prop) (hw : 0 < w)
    (fits : 1 + max result.encoding.words state.encoding.words < 2 ^ w)
    {f : A → OracleComp spec (B ⊕ A)} {g : A → OracleComp spec B} {body stop : Code w}
    (bodyRefines : ∀ remaining, RefinesOn (invariant (remaining + 1)) port cost state (result.sum state hw fits) f body)
    (stopRefines : RefinesOn (invariant 0) port cost state result g stop)
    (preserves : ∀ remaining value, invariant (remaining + 1) value →
      ∀ answer ∈ support (f value), Sum.elim (fun _ => True) (invariant remaining) answer)
    (fuel : Nat) :
    RefinesOn (invariant fuel) port cost state result (BackendProgram.loopDenote f g fuel)
      (Interactive.loop body stop result.encoding.words state.encoding.words fuel) := by
  induction fuel with
  | zero => exact stopRefines
  | succ fuel ih =>
    have refined := (bodyRefines fuel).seq
      (RefinesOn.dispatch result state result
        ((Refines.compute port cost (Realizer.identity hw result)).on (fun _ => True)) ih hw fits)
      (preserves fuel)
    convert refined using 1
    · funext value
      rw [BackendProgram.loopDenote]
      congr 1
      funext answer
      cases answer <;> rfl
    · rfl

end Interactive
end Signatures.Runtime.CaliperBackend
