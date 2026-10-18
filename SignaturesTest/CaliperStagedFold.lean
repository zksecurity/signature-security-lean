import Signatures.Runtime.Caliper.ExpressionCompilation
import Lean

open Caliper Signatures.Runtime Signatures.Runtime.CaliperBackend
open Signatures.Runtime.CaliperBackend.BoundedSource
open Signatures.Runtime.CaliperBackend.SourceExpression

namespace SignaturesTest.CaliperStagedFold

private def base (_ : Unit) : Type := Word 8
private def Op (_ _ : Ty Unit) : Type := Empty
private def primitives : Primitives base Op where
  execute instr := nomatch instr
  cost instr := nomatch instr
private abbrev Cert {Γ : List (Ty Unit)} {a : Ty Unit} (expression : Expr Op Γ a)
    (input : Layout 8 (Env base Γ)) (output : Layout 8 (a.Value base)) :=
  Compilation primitives .unit (by decide) expression input output

private def unit := DataImplementation.unitLayout 8
private def entry := Layout.counter 8 10 (by decide) (by decide)
private def list := entry.boundedList 3 (by decide) (by decide)
private def input := list.prod unit (by decide)
private def states (i : Fin 4) : Layout 8 (List Nat) :=
  entry.boundedList i.val (by omega) (by change 1 + i.val * 1 < 256; omega)
private theorem argFits (i : Fin 3) :
    entry.representation.encoding.words + (states i.castSucc).representation.encoding.words + input.representation.encoding.words < 2 ^ 8 := by
  change 1 + (1 + i.val * 1) + 4 < 256
  omega
private theorem frameFits (i : Fin 4) :
    1 + (3 - i.val) * entry.representation.encoding.words + (states i).representation.encoding.words +
      2 * input.representation.encoding.words < 2 ^ 8 := by
  change 1 + (3 - i.val) * 1 + (1 + i.val * 1) + 2 * 4 < 256
  omega
private def body : Expr Op [.nat, .list .nat, .list .nat] (.list .nat) :=
  .cons (.var .here) (.var (.there .here))

-- The same source body compiles at each stage. Its accumulator physically
-- grows from one stored header word to a header plus three entries.
private def bodyCode (i : Fin 3) : Cert body
    (FoldImplementation.bodyInput entry (states i.castSucc) input (argFits i)) (states i.succ) := by
  refine Compilation.cons (w := 8) (P := primitives) (cost := .unit) (hw := by decide)
    (Γ := [.nat, .list .nat, .list .nat]) (a := .nat) entry i.val ?_ ?_
    (Compilation.var (P := primitives) (w := 8) (hw := by decide)
      (Variable.here (base := base) (Γ := [.list .nat, .list .nat]) (a := .nat)
        entry ((states i.castSucc).prod input ?_) ?_))
    (Compilation.var (P := primitives) (w := 8) (hw := by decide)
      (Variable.there (base := base) (b := .nat) entry
        (Variable.here (base := base) (Γ := [.list .nat]) (a := .list .nat) (states i.castSucc) input ?_) ?_)) ?_ ?_
  all_goals change _ < 256
  all_goals dsimp [FoldImplementation.bodyInput, Layout.prod, Representation.transport, Encoding.transport,
    Representation.prod, Encoding.prod, Encoding.checked, states, Layout.boundedList,
    Representation.boundedList, Encoding.boundedList, entry, Layout.counter, Representation.fin,
    input, list, unit, DataImplementation.unitLayout, Layout.all, Encoding.fin, Encoding.unit]
  all_goals omega

private def stops (i : Fin 4) : Implementation .unit (states i) list id :=
  ListData.widen .unit (by decide) entry i.val 3 (by omega) (by decide) (by decide) (by decide)
private def expression : Expr Op [.list .nat] (.list .nat) :=
  .fold (.var .here) .nil body
private def certificate : Cert expression input list := by
  refine Compilation.foldStages (w := 8) (P := primitives) (cost := .unit) (hw := by decide)
    (Γ := [.list .nat]) (a := .nat) (b := .list .nat) input entry list 3 states (by decide) argFits frameFits
    (Compilation.var (P := primitives) (w := 8) (hw := by decide)
      (Variable.here (base := base) (Γ := []) (a := .list .nat) list unit ?_))
    (Compilation.nil (w := 8) (P := primitives) (cost := .unit) (hw := by decide)
      (Γ := [.list .nat]) (a := .nat) input entry 0 ?_ ?_) bodyCode stops <;> decide

private def observe (value : input.Value) := do
  let implementation ← certificate.compile (by decide)
  let initial := input.representation.initial value
  let before := { initial with
    bufs := fun buffer => if buffer = 200 then #[77] else initial.bufs buffer
    caps := fun buffer => if buffer = 200 then 1 else initial.caps buffer }
  let (state, time, net, peak) ← Caliper.run .unit RandomTape.zero 10000 implementation.program.code before
  pure ((state.bufs 0, state.bufs 200), (state.caps 200,
    (List.range 24).all (fun i => state.caps (i + 1) == 0)), (time, net, peak))

private def emptyInput : input.Value := ⟨([], ()), by change (0 ≤ 3 ∧ _) ∧ True; simp⟩
private def partialInput : input.Value := ⟨([2], ()), by change (1 ≤ 3 ∧ ∀ value ∈ [2], value < 10) ∧ True; simp⟩
private def fullInput : input.Value := ⟨([2, 5, 7], ()), by change (3 ≤ 3 ∧ ∀ value ∈ [2, 5, 7], value < 10) ∧ True; simp⟩

-- Early return still executes the final padding conversion. Complete runs
-- preserve unrelated storage and release every generated temporary buffer.
example : observe emptyInput = some ((#[0, 0, 0, 0], #[77]), (1, true), (818, 0, 18)) := by decide +kernel
example : observe partialInput = some ((#[1, 2, 0, 0], #[77]), (1, true), (1599, 0, 27)) := by decide +kernel
example : observe fullInput = some ((#[3, 7, 5, 2], #[77]), (1, true), (3447, 0, 33)) := by decide +kernel
example : (observe ⟨([2, 5], ()), by change (2 ≤ 3 ∧ ∀ value ∈ [2, 5], value < 10) ∧ True; simp⟩).map
    (fun result => result.1.1) = some #[2, 5, 2, 0] := by decide +kernel

example : expression.denote primitives ([2, 5, 7], ()) = [7, 5, 2] := rfl

open Lean in
run_cmd do
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``FoldStep.exec, ``FoldStep.realizer, ``FoldStep.descriptionFits,
      ``FoldStep.time_unit_le, ``FoldStep.code_descriptionWords_le,
      ``StagedFold.step, ``StagedFold.finish, ``StagedFold.compile,
      ``Compilation.compile, ``Compilation.exec, ``bodyCode, ``stops, ``certificate] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"

end SignaturesTest.CaliperStagedFold
