import Proofs.Runtime.Caliper.CacheReadMemory
import Lean

open Caliper OracleComp OracleSpec Signatures.Runtime Signatures.Runtime.CaliperBackend
open Signatures.Runtime.CaliperBackend.BoundedSource

namespace SignaturesTest.CaliperCacheRead

private def base (_ : Unit) : Type := Word 8
private inductive Op : Ty Unit → Ty Unit → Type
  | equal : Op (.pair .nat .nat) .bool
private def primitives : Primitives base Op where
  execute instruction := match instruction with | .equal => fun value => decide (value.1 = value.2)
  cost _ _ := 1
private def comparison : Expr Op [.nat, .nat] .bool := .op .equal (.pair (.var .here) (.var (.there .here)))
private theorem comparison_correct (left right : Nat) :
    comparison.denote primitives (left, right, ()) = decide (left = right) := rfl

private def counter := Layout.counter 8 256 (by decide) (by decide)
private def layout : CacheLayout 8 Nat Nat where
  key := counter
  value := counter
  capacityPred := 1
  wordFits := by decide
  countFits := by decide
  storageFits := by decide

private def sampleSpec : OracleSpec Unit := fun _ => counter.Value
private def replyView : (Σ _ : layout.lookup.unit.Value, counter.Value) ≃ counter.Value where
  toFun := Sigma.snd
  invFun value := ⟨⟨(), trivial⟩, value⟩
  left_inv value := by rcases value with ⟨⟨position, valid⟩, answer⟩; cases position; rfl
  right_inv _ := rfl
private def port : Interactive.Port 8 sampleSpec where
  Request := layout.lookup.unit.Value
  source _ := ()
  request := layout.lookup.unit.representation
  reply := counter.representation.transport replyView
private def drawSource : OracleComp sampleSpec counter.Value := queryBind () Pure.pure
private def draw : Interactive.Code 8 := .query

private theorem draw_correct : Interactive.Refines port .unit layout.lookup.unit.representation counter.representation
    (fun _ => drawSource) draw := by
  have projected := (Interactive.Refines.query port .unit).viewOutput counter.representation
    (fun packet => packet.2) (fun _ => rfl)
  convert projected using 1 <;> rfl

private theorem draw_time : Interactive.TimeBound port .unit layout.lookup.unit.representation draw 4 := Interactive.TimeBound.query
private theorem draw_words : (draw.lower port).descriptionWords ≤ 20 := by decide +kernel
private theorem draw_names : WordIO.NamesBound (draw.lower port) 3 := by constructor <;> decide +kernel
private theorem draw_fits : (draw.lower port).DescriptionFits := by
  exact WordIO.exchange_descriptionFits (w := 8) 0 1 (by decide) (by decide)

private inductive Cmd : Ty Unit → Ty Unit → Type
  | sample : Cmd .unit .nat
private def semantics : SemanticsM base Cmd (OracleComp sampleSpec) := fun command => match command with
  | .sample => fun _ => Subtype.val <$> drawSource

private def program := EncodedCacheRead.code (base := base) (key := .nat) (val := .nat)
  layout primitives comparison comparison_correct port draw

private theorem time_eq : EncodedCacheRead.timeBudget (base := base) (key := .nat) (val := .nat) layout 4 = 15437 := by decide +kernel
private theorem words_eq : EncodedCacheRead.codeBudget (base := base) (key := .nat) (val := .nat) layout 20 = 56159 := by decide +kernel

private theorem bounded : Interactive.TimeBound port .unit layout.input.representation program 15437 := by
  rw [← time_eq]
  exact EncodedCacheRead.time_bound (base := base) (key := .nat) (val := .nat)
    layout primitives comparison comparison_correct port draw_correct draw_time

example : (program.lower port).descriptionWords ≤ 56159 := by
  rw [← words_eq]
  exact EncodedCacheRead.code_bound (base := base) (key := .nat) (val := .nat)
    layout primitives comparison comparison_correct port draw draw_words
example : (program.lower port).DescriptionFits :=
  EncodedCacheRead.descriptionFits (base := base) (key := .nat) (val := .nat)
    layout primitives comparison comparison_correct port draw draw_fits draw_names (by decide)
example : (program.lower port).staticWords 201 201 ≤ 281619 := by
  have bound := EncodedCacheRead.staticMemory (base := base) (key := .nat) (val := .nat)
    layout primitives comparison comparison_correct port draw draw_words draw_names 201 201
  rw [words_eq] at bound
  exact bound

private theorem valid_iff (key value : Nat) (entries : List (Nat × Nat)) :
    layout.input.valid (key, value, entries, ()) ↔
      (key < 256 ∧ value < 256 ∧ entries.length ≤ 2 ∧ ∀ entry ∈ entries, entry.1 < 256 ∧ entry.2 < 256) ∧
      ((lookupValue key value entries).1 = false → entries.length ≤ 1) := by
  change ((key < 256 ∧ value < 256 ∧ (entries.length ≤ 2 ∧ ∀ entry ∈ entries, entry.1 < 256 ∧ entry.2 < 256) ∧ True) ∧
    ((lookupValue key value entries).1 = false → entries.length ≤ 1)) ↔ _
  tauto

private def fullHit : layout.input.Value := ⟨(2, 42, [(1, 7), (2, 0)], ()), by rw [valid_iff]; decide +kernel⟩
private def miss : layout.input.Value := ⟨(2, 42, [(1, 7)], ()), by rw [valid_iff]; decide +kernel⟩
private def empty : layout.input.Value := ⟨(2, 42, [], ()), by rw [valid_iff]; decide +kernel⟩

private def run (value : layout.input.Value) (replies : List (Word 8)) := do
  let initial := layout.input.representation.initial value
  let before := { initial with
    regs := fun register => if register = 200 then 99 else initial.regs register
    bufs := fun buffer => if buffer = 200 then #[77] else initial.bufs buffer
    caps := fun buffer => if buffer = 200 then 1 else initial.caps buffer
    tapePos := 7 }
  let result ← WordIO.run .unit RandomTape.zero 30000 (program.lower port) before replies
  pure ((result.state.bufs 0, result.state.bufs 200, result.state.regs 200, result.state.tapePos), result.trace, result.remaining)

-- Hits work on full tables, preserve cached zero, and consume no oracle input.
example : run fullHit [88] = some ((#[0, 2, 1, 7, 2, 0], #[77], 99, 7), [], [88]) := by decide +kernel
example : run fullHit [] = some ((#[0, 2, 1, 7, 2, 0], #[77], 99, 7), [], []) := by decide +kernel
-- Misses consume exactly the primitive's reply and use it, rather than the default.
example : run miss [9, 88] = some ((#[9, 2, 2, 9, 1, 7], #[77], 99, 7), [.invoke, .input 9], [88]) := by decide +kernel
example : run empty [0] = some ((#[0, 1, 2, 0, 0, 0], #[77], 99, 7), [.invoke, .input 0], []) := by decide +kernel
example : run miss [] = none := by decide +kernel
example : ¬layout.input.valid (3, 42, [(1, 7), (2, 0)], ()) := by rw [valid_iff]; decide +kernel

-- Source equality is uniform over all admitted tables, tapes and adaptive replies.
example (tape : RandomTape 8) (value : layout.input.Value) :
    (fun result => Subtype.val <$> Interactive.observe (CacheRead.output layout).representation result) <$>
      program.execute port .unit tape (layout.input.representation.initial value) =
        some <$> (cacheGetExpr comparison Cmd.sample).denote primitives semantics value.val :=
  EncodedCacheRead.observe (base := base) (key := .nat) (val := .nat) layout primitives comparison comparison_correct
    semantics Cmd.sample port drawSource draw draw_correct rfl tape value _ (layout.input.representation.initial_holds value)

open Lean in
run_cmd do
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``Implementation.pair_boundedBy, ``Implementation.pair_buffers, ``Implementation.pair_names,
      ``CacheRead.hit, ``CacheRead.finish, ``CacheRead.hit_bounded, ``CacheRead.finish_bounded,
      ``CacheRead.draw_refines, ``CacheRead.miss_refines, ``CacheRead.branch_refines,
      ``EncodedCacheRead.refines, ``EncodedCacheRead.source_eq, ``EncodedCacheRead.observe,
      ``EncodedCacheRead.time_bound, ``EncodedCacheRead.code_bound, ``EncodedCacheRead.names,
      ``EncodedCacheRead.descriptionFits, ``EncodedCacheRead.staticMemory, ``EncodedCacheRead.memoryBound,
      ``Interactive.retain_names, ``Interactive.dispatch_names, ``draw_correct, ``bounded] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"

end SignaturesTest.CaliperCacheRead
