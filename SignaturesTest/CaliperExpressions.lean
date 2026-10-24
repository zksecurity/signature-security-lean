import Proofs.Runtime.Caliper
import Lean

open Caliper Signatures.Runtime Signatures.Runtime.CaliperBackend
open Signatures.Runtime.CaliperBackend.BoundedSource
open Signatures.Runtime.CaliperBackend.SourceExpression

namespace SignaturesTest.CaliperExpressions

private def base (_ : Unit) : Type := Word 8
private inductive Op : Ty Unit → Ty Unit → Type
  | equal : Op (.pair .nat .nat) .bool
  | subtract : Op (.pair .nat .nat) .nat
  | release : Op .nat .nat
private def primitives : Primitives base Op where
  execute instr value := match instr with
    | .equal => decide (value.1 = value.2)
    | .subtract => value.1 - value.2
    | .release => value
  cost _ _ := 1
private abbrev Cert {Γ : List (Ty Unit)} {a : Ty Unit} (expression : Expr Op Γ a)
    (input : Layout 8 (Env base Γ)) (output : Layout 8 (a.Value base)) :=
  Compilation primitives .unit (by decide) expression input output

private def unit := DataImplementation.unitLayout 8
private def counter := Layout.counter 8 256 (by decide) (by decide)
private def small := Layout.counter 8 10 (by decide) (by decide)
private def boolean := DataImplementation.boolLayout 8 (by decide)
private def tail := counter.prod unit (by decide)
private def input := counter.prod tail (by decide)
private def x : Expr Op [.nat, .nat] .nat := .var .here
private def y : Expr Op [.nat, .nat] .nat := .var (.there .here)
private def xCode : Cert x input counter := by
  refine Compilation.var (P := primitives) (w := 8) (hw := by decide)
    (Variable.here (base := base) (Γ := [.nat]) (a := .nat) counter tail ?_)
  decide
private def yCode : Cert y input counter := by
  refine Compilation.var (P := primitives) (w := 8) (hw := by decide)
    (Variable.there (base := base) (b := .nat) counter (Variable.here (base := base) (Γ := []) (a := .nat) counter unit ?_) ?_) <;> decide
private def pairCode : Cert (.pair x y) input (counter.prod counter (by decide)) :=
  .pair xCode yCode (by decide) (by decide) (by decide)
private def difference : Expr Op [.nat, .nat] .nat := .op .subtract (.pair x y)
private def differenceCode : Cert difference input counter := by
  unfold difference
  refine .op .subtract ?_ pairCode
  exact Natural.subtract .unit 256 256 (by decide) (by decide) (by decide)
private def equalCode : Cert (.op .equal (.pair x y)) input boolean :=
  .op .equal (Natural.equal .unit 256 256 (by decide) (by decide) (by decide)) pairCode
private def choice : Expr Op [.nat, .nat] .nat := .branch (.op .equal (.pair x y)) (.nat 11) difference
private def choiceCode : Cert choice input counter := by
  refine .branch equalCode (Compilation.nat (w := 8) (P := primitives) (cost := .unit) (hw := by decide) (Γ := [.nat, .nat]) input 11 256 ?_ ?_) differenceCode ?_ ?_ <;> decide

private def observe {Γ : List (Ty Unit)} {a : Ty Unit} {expression : Expr Op Γ a}
    {input : Layout 8 (Env base Γ)} {output : Layout 8 (a.Value base)}
    (certificate : Cert expression input output) (value : input.Value) := do
  let implementation ← certificate.compile (by decide)
  let (state, time, net, peak) ← Caliper.run .unit RandomTape.zero 3000 implementation.program.code
    (input.representation.initial value)
  pure (state.bufs 0, time, net, peak)

example : observe differenceCode ⟨(200, 150, ()), by change _ < _ ∧ _ < _ ∧ True; decide⟩ =
    some (#[50], 188, 0, 6) := by decide +kernel
example : observe choiceCode ⟨(200, 150, ()), by change _ < _ ∧ _ < _ ∧ True; decide⟩ =
    some (#[50], 569, 0, 8) := by decide +kernel
example : observe choiceCode ⟨(255, 255, ()), by change _ < _ ∧ _ < _ ∧ True; decide⟩ =
    some (#[11], 388, -1, 8) := by decide +kernel
example : choice.denote primitives (200, 150, ()) = 50 := rfl

private def literals : Expr Op [] (.pair .nat .nat) := .pair (.nat 2) (.nat 7)
private def literalCode : Cert literals unit (small.prod small (by decide)) := by
  refine .pair (Compilation.nat (w := 8) (P := primitives) (cost := .unit) (hw := by decide) (Γ := []) unit 2 10 ?_ ?_)
    (Compilation.nat (w := 8) (P := primitives) (cost := .unit) (hw := by decide) (Γ := []) unit 7 10 ?_ ?_) ?_ ?_ ?_ <;> decide
private def firstCode : Cert (.fst literals) unit small := by
  refine Compilation.fst (w := 8) (P := primitives) (cost := .unit) (hw := by decide) (a := .nat) (b := .nat)
    small small ?_ literalCode
  decide
private def secondCode : Cert (.snd literals) unit small := by
  refine Compilation.snd (w := 8) (P := primitives) (cost := .unit) (hw := by decide) (a := .nat) (b := .nat)
    small small ?_ literalCode
  decide
private def bindingCode : Cert (Γ := []) (.letE (.nat 7) (.var .here)) unit small := by
  refine .letE small ?_ ?_ (Compilation.nat (w := 8) (P := primitives) (cost := .unit) (hw := by decide) (Γ := []) unit 7 10 ?_ ?_)
    (Compilation.var (P := primitives) (w := 8) (hw := by decide)
    (Variable.here (base := base) (Γ := []) (a := .nat) small unit ?_)) <;> decide
private def wideBindingCode : Cert (Γ := []) (.letE (.nat 7) (.var .here)) unit counter :=
  .view bindingCode (by intro value valid; change value < 10 at valid; change value < 256; exact valid.trans_le (by decide : 10 ≤ 256)) (fun _ => rfl)
example : observe firstCode ⟨(), trivial⟩ = some (#[2], 74, 1, 5) := by decide +kernel
example : observe secondCode ⟨(), trivial⟩ = some (#[7], 74, 1, 5) := by decide +kernel
example : observe wideBindingCode ⟨(), trivial⟩ = some (#[7], 51, 1, 3) := by decide +kernel
private def boolCode : Cert (Γ := []) (.bool true) unit boolean := Compilation.bool (w := 8) (P := primitives) (cost := .unit) (hw := by decide) (Γ := []) unit true
private def unitCode : Cert (Γ := []) .unit unit unit := Compilation.unit (w := 8) (P := primitives) (cost := .unit) (hw := by decide) (Γ := []) unit
example : observe boolCode ⟨(), trivial⟩ = some (#[1], 7, 1, 2) := by decide
example : observe unitCode ⟨(), trivial⟩ = some (#[], 0, 0, 0) := by decide

private def list := small.boundedList 2 (by decide) (by decide)
private def listInput := list.prod unit (by decide)
private def consCode : Cert (Γ := []) (.cons (.nat 7) .nil) unit (small.boundedList 1 (by decide) (by decide)) := by
  refine Compilation.cons (w := 8) (P := primitives) (cost := .unit) (hw := by decide) (Γ := []) (a := .nat) small 0 ?_ ?_ (Compilation.nat (w := 8) (P := primitives) (cost := .unit) (hw := by decide) (Γ := []) unit 7 10 ?_ ?_)
    (Compilation.nil (w := 8) (P := primitives) (cost := .unit) (hw := by decide) (Γ := []) (a := .nat) unit small 0 ?_ ?_) ?_ ?_ <;> decide
private def widenedCode : Cert (Γ := []) (.cons (.nat 7) .nil) unit list :=
  Compilation.listWiden (w := 8) (P := primitives) (cost := .unit) (hw := by decide) (Γ := []) (a := .nat) small 1 2 (by decide) (by decide) (by decide) consCode
example : (observe widenedCode ⟨(), trivial⟩).map (fun result => result.1) = some #[1, 7, 0] := by decide +kernel

private def foldExpr : Expr Op [.list .nat] .nat := .fold (.var .here) (.nat 0) (.var .here)
private def foldCode : Cert foldExpr listInput small := by
  refine Compilation.fold (w := 8) (P := primitives) (cost := .unit) (hw := by decide) (Γ := [.list .nat]) (a := .nat) (b := .nat) listInput small small 2 ?_ ?_ ?_
    (Compilation.var (P := primitives) (w := 8) (hw := by decide)
    (Variable.here (base := base) (Γ := []) (a := .list .nat) list unit ?_))
    (Compilation.nat (w := 8) (P := primitives) (cost := .unit) (hw := by decide) (Γ := [.list .nat]) listInput 0 10 ?_ ?_)
    (Compilation.var (P := primitives) (w := 8) (hw := by decide)
    (Variable.here (base := base) (Γ := [.nat, .list .nat]) (a := .nat) small (small.prod listInput ?_) ?_)) <;> decide
example : (observe foldCode ⟨([], ()), by change (0 ≤ 2 ∧ _) ∧ True; simp⟩).map (fun result => result.1) =
    some #[0] := by decide +kernel
example : (observe foldCode ⟨([2], ()), by change (1 ≤ 2 ∧ ∀ value ∈ [2], value < 10) ∧ True; simp⟩).map (fun result => result.1) =
    some #[2] := by decide +kernel
example : (observe foldCode ⟨([2, 7], ()), by change (2 ≤ 2 ∧ ∀ value ∈ [2, 7], value < 10) ∧ True; simp⟩).map (fun result => result.1) =
    some #[7] := by decide +kernel

-- The primitive fits by itself. Its use of the final available buffer means
-- that an enclosing pair cannot allocate a disjoint saved-input buffer.
private def releaseLast : Realizer .unit counter.representation counter.representation id where
  code := .memFree 255
  positive_width := by decide
  description_fits := by simp [DescriptionFits, description]
  random_free := trivial
  time _ := 0
  net _ := 0
  workspace _ := 0
  correct tape value before represented := by
    have execution : Caliper.Exec .unit tape (.memFree 255) before (before.allocBuf 255 0)
        0 (-(before.caps 255 : Int)) 0 := .memFree
    refine ⟨before.allocBuf 255 0, _, _, execution, ?_, by omega, le_rfl⟩
    exact ⟨represented.1, by simpa using represented.2.1,
      execution.wellFormed_preserved represented.2.2.1,
      CapacitiesFit.allocBuf represented.2.2.2 255 0 (by decide)⟩
private def release : Implementation .unit counter counter id where
  preserves _ valid := valid
  program := releaseLast
private def releaseCode : Cert (.op .release x) input counter := .op .release release xCode
private def rejected : Cert (.pair (.op .release x) y) input (counter.prod counter (by decide)) :=
  .pair releaseCode yCode (by decide) (by decide) (by decide)
example : (releaseCode.compile (by decide)).isSome = true := by decide
example : rejected.compile (by decide) = none := rfl

-- Budgets are supplied only for the primitive leaves. The compiler derives
-- every constructor's copying, control and stored-program overhead.
private def differenceBounds : differenceCode.LocalBounds :=
  (((), ()), ⟨⟨8, 38⟩,
    ⟨fun value => (Natural.subtract_time_unit 256 256 (by decide) (by decide) (by decide) value).le, by decide⟩⟩)
private def equalBounds : equalCode.LocalBounds :=
  (((), ()), ⟨⟨6, 27⟩,
    ⟨fun value => (Natural.equal_time_unit 256 256 (by decide) (by decide) (by decide) value).le, by decide⟩⟩)
private def choiceBounds : choiceCode.LocalBounds := (equalBounds, (), differenceBounds)
private def releaseBounds : releaseCode.LocalBounds := ((), ⟨⟨0, 2⟩, ⟨fun _ => le_rfl, le_rfl⟩⟩)
private def rejectedBounds : rejected.LocalBounds := (releaseBounds, ())

example : (differenceCode.budget differenceBounds).time = 188 ∧
    (differenceCode.budget differenceBounds).words = 791 := by decide
example : (choiceCode.budget choiceBounds).time = 576 ∧
    (choiceCode.budget choiceBounds).words = 2456 := by decide

private def accepted {Γ : List (Ty Unit)} {a : Ty Unit} {expression : Expr Op Γ a}
    {input : Layout 8 (Env base Γ)} {output : Layout 8 (a.Value base)}
    (certificate : Cert expression input output) (bounds : certificate.LocalBounds) : Bool :=
  (certificate.compileBudget bounds).isSome

example : [accepted differenceCode differenceBounds, accepted choiceCode choiceBounds,
    accepted firstCode ((), ()), accepted secondCode ((), ()), accepted bindingCode ((), ()),
    accepted wideBindingCode ((), ()), accepted boolCode (), accepted unitCode (),
    accepted consCode ((), ()), accepted widenedCode ((), ()), accepted foldCode ((), (), ()),
    accepted releaseCode releaseBounds] = List.replicate 12 true := by decide +kernel
example : rejected.compileBudget rejectedBounds = none := rfl
example : Subtype.val <$> choiceCode.compileBudget choiceBounds = choiceCode.compile (by decide) :=
  choiceCode.compileBudget_forget choiceBounds

-- Two code words can name the final buffer. A code-length budget cannot
-- replace a primitive's dense descriptor reservation.
example : descriptionWords releaseLast.code = 2 ∧ releaseLast.code.memBound = 256 := by decide
example : ¬ NamesAccounted releaseLast.code 0 := by
  intro bound
  have impossible : 256 ≤ 2 := bound.buffers
  omega
private theorem releaseNames : releaseCode.PrimitiveNames 256 :=
  ⟨trivial, ⟨by decide, by decide⟩⟩
private theorem differenceNames : differenceCode.PrimitiveNames 4 :=
  ⟨⟨trivial, trivial⟩, ⟨by decide, by decide⟩⟩
private theorem equalNames : equalCode.PrimitiveNames 4 :=
  ⟨⟨trivial, trivial⟩, ⟨by decide, by decide⟩⟩
private theorem choiceNames : choiceCode.PrimitiveNames 4 :=
  ⟨equalNames, trivial, differenceNames⟩
private theorem choiceAccepted : (choiceCode.compile (by decide)).isSome := by decide +kernel
private def choiceProgram := (choiceCode.compile (by decide)).get choiceAccepted

example : NamesBound choiceProgram.program.code 2460 :=
  choiceCode.nameBounds choiceBounds choiceNames choiceProgram (Option.eq_some_of_isSome choiceAccepted)
example : staticWords choiceProgram.program.code 4 201 ≤ 12296 :=
  choiceCode.staticMemory_bound choiceBounds choiceNames choiceProgram (Option.eq_some_of_isSome choiceAccepted) 4 201

-- The theorem applies to every represented input and includes all caller-owned
-- capacity, even in buffer 200, through every intermediate and final state.
example (tape : RandomTape 8) (value : input.Value) (before : State 8)
    (represented : input.representation.Holds value before)
    (registers : RegisterBound before 4) (buffers : before.SupportBound 201) :
    ∃ after net peak, Caliper.Exec .unit tape choiceProgram.program.code before after
        (choiceProgram.program.time value) net peak ∧
      ∀ between, (Caliper.Reaches .unit tape choiceProgram.program.code before between ∨ between = after) →
        (staticWords choiceProgram.program.code 4 201 : Int) +
          between.liveMem (max 201 choiceProgram.program.code.memBound) ≤ 12872 + before.liveMem 201 := by
  obtain ⟨after, net, peak, execution, _, _, memory⟩ :=
    choiceCode.memoryBound choiceBounds choiceNames choiceProgram (Option.eq_some_of_isSome choiceAccepted)
      tape value before represented 4 201 registers buffers
  refine ⟨after, net, peak, execution, ?_⟩
  intro between visited
  have bound := (memory between visited).2.2.2
  change _ ≤ ((12296 + before.liveMem 201 + 576 : Nat) : Int) at bound
  omega

open Lean in
run_cmd do
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``ListData.empty, ``ListData.cons, ``ListData.widen, ``Implementation.view,
      ``Implementation.castFunction, ``Implementation.checkedPair, ``Implementation.checkedBranch,
      ``Variable.compile, ``Compilation.compile, ``Compilation.exec, ``differenceCode,
      ``choiceCode, ``firstCode, ``secondCode, ``bindingCode, ``wideBindingCode,
      ``boolCode, ``unitCode, ``consCode, ``widenedCode, ``foldCode, ``releaseLast, ``releaseCode, ``rejected,
      ``differenceBounds, ``equalBounds, ``choiceBounds, ``releaseBounds, ``rejectedBounds,
      ``Compilation.budget, ``Compilation.bounded, ``Compilation.exec_bounded,
      ``Compilation.compileBudget, ``Compilation.compileBudget_forget,
      ``releaseNames, ``differenceNames, ``equalNames, ``choiceNames,
      ``Retain.names, ``Pairing.names, ``Compilation.PrimitiveNames, ``Compilation.names,
      ``Compilation.nameBounds, ``Compilation.staticMemory_bound, ``Compilation.memoryBound,
      ``LocalReach.total_memory_bound, ``Budget.staticMemory_le] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"

end SignaturesTest.CaliperExpressions
