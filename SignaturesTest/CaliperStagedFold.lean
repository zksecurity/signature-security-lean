import Signatures.Runtime.Caliper.ExpressionCompilation
import Signatures.Runtime.Caliper.StagedFoldBounds
import Signatures.Runtime.Caliper.StructuralBudgets
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

private theorem bodyAccepted (i : Fin 3) : ((bodyCode i).compile (by decide)).isSome := by
  fin_cases i <;> decide +kernel
private def bodyPrograms (i : Fin 3) := ((bodyCode i).compile (by decide)).get (bodyAccepted i)
private theorem bodyCompiledBound (i : Fin 3)
    (implementation : Implementation .unit (FoldImplementation.bodyInput entry (states i.castSucc) input (argFits i))
      (states i.succ) (body.denote primitives))
    (compiled : (bodyCode i).compile (by decide) = some implementation) : implementation.BoundedBy 625 2221 := by
  dsimp only [bodyCode, Compilation.compile] at compiled
  erw [Option.bind_eq_some_iff] at compiled
  obtain ⟨head, headEq, compiled⟩ := compiled
  erw [Option.bind_eq_some_iff] at compiled
  obtain ⟨tail, tailEq, compiled⟩ := compiled
  erw [Option.bind_eq_some_iff] at compiled
  obtain ⟨frame, frameEq, resultEq⟩ := compiled
  cases Option.some.inj headEq
  cases Option.some.inj tailEq
  have tailFits : (states i.castSucc).representation.encoding.words + input.representation.encoding.words < 2 ^ 8 := by
    change (1 + i.val * 1) + 4 < 256
    omega
  have argumentFits : entry.representation.encoding.words + ((states i.castSucc).prod input tailFits).representation.encoding.words < 2 ^ 8 := by
    change 1 + ((1 + i.val * 1) + 4) < 256
    omega
  have headBound := Implementation.first_boundedBy entry ((states i.castSucc).prod input tailFits) (by decide) argumentFits
  have tailBound := ((Implementation.second_boundedBy entry ((states i.castSucc).prod input tailFits) (by decide) argumentFits).then
    (Implementation.first_boundedBy (states i.castSucc) input (by decide) tailFits)).mono
      (show 8 * ((states i.castSucc).prod input tailFits).representation.encoding.words + 8 * (states i.castSucc).representation.encoding.words ≤ 80 by
        change 8 * ((1 + i.val * 1) + 4) + 8 * (1 + i.val * 1) ≤ 80
        omega)
      (show _ ≤ 289 by
        change (26 * ((1 + i.val * 1) + 4) + 14) + (26 * (1 + i.val * 1) + 14) + 1 ≤ 289
        omega)
  have pairBound := Implementation.checkedPair_boundedBy _ _ (by decide) _ _ _ 8 40 80 289
    headBound tailBound frame frameEq
  have pairBudget := pairBound.mono (show _ ≤ 588 by
    change 8 + 80 + 52 * (1 + ((1 + i.val * 1) + 4)) + 36 * 1 + 16 * (1 + i.val * 1) ≤ 588
    omega) (show _ ≤ 2078 by
    change 40 + 289 + 169 * (1 + ((1 + i.val * 1) + 4)) + 117 * 1 + 52 * (1 + i.val * 1) + 124 ≤ 2078
    omega)
  have consBudget := (ListData.cons_boundedBy entry i.val (by decide)
    (by change i.val + 1 < 256; omega) (by change 1 + (i.val + 1) * 1 < 256; omega)).mono
      (show _ ≤ 37 by change 8 * (1 + (i.val + 1) * 1) + 5 ≤ 37; omega)
      (show _ ≤ 142 by change 26 * (1 + (i.val + 1) * 1) + 38 ≤ 142; omega)
  erw [← Option.some.inj resultEq]
  exact pairBudget.then consBudget
private theorem bodiesBounded (i : Fin 3) : (bodyPrograms i).BoundedBy 625 2221 :=
  bodyCompiledBound i (bodyPrograms i) (Option.eq_some_of_isSome (bodyAccepted i))
private theorem stopsBounded (i : Fin 4) : (stops i).BoundedBy 32 118 := by
  fin_cases i
  · constructor
    · intro value; change 29 ≤ 32; decide
    · decide
  · constructor
    · intro value; change 30 ≤ 32; decide
    · decide
  · constructor
    · intro value; change 31 ≤ 32; decide
    · decide
  · constructor
    · intro value; change 32 ≤ 32; decide
    · decide

private def folded := StagedFold.compile (by decide) entry list input (by decide) (body.denote primitives)
  3 states (by decide) argFits frameFits (fun i => (bodyCode i).compile (by decide)) stops
private theorem foldedAccepted : folded.isSome := by decide +kernel
private def foldedProgram := folded.get foldedAccepted

-- These bounds cover every represented fold input, not just the concrete
-- examples below. The generated fold budget follows from the per-stage budgets.
private theorem foldedBounded : foldedProgram.BoundedBy 6412 24333 := by
  apply StagedFold.compile_boundedBy entry list input (by decide) (body.denote primitives)
    3 states (by decide) argFits frameFits (fun i => (bodyCode i).compile (by decide)) stops
    4 625 2221 32 118 (by decide) (by decide) ?_ ?_ stopsBounded foldedProgram
      (Option.eq_some_of_isSome foldedAccepted)
  · intro i
    change 1 + i.val * 1 ≤ 4
    omega
  · intro i implementation compiled
    have equal : bodyPrograms i = implementation := Option.get_of_eq_some (bodyAccepted i) compiled
    exact equal ▸ bodiesBounded i

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
      ``Implementation.BoundedBy.then, ``Implementation.BoundedBy.exec,
      ``Implementation.first_boundedBy, ``Implementation.second_boundedBy,
      ``Implementation.checkedPair_boundedBy, ``ListData.cons_boundedBy,
      ``StagedFold.finish_boundedBy, ``StagedFold.step_boundedBy, ``StagedFold.compile_boundedBy,
      ``Compilation.compile, ``Compilation.exec, ``bodyCode, ``stops, ``certificate,
      ``bodiesBounded, ``stopsBounded, ``foldedBounded] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"

end SignaturesTest.CaliperStagedFold
