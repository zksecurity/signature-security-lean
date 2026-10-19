import Signatures.Runtime.Caliper.SchnorrAGMCacheLayout
import Lean

open Caliper OracleComp OracleSpec Signatures.Runtime Signatures.Runtime.CaliperBackend BoundedSource
namespace SignaturesTest.CaliperStatefulCache

private def base (_ : Unit) : Type := Word 16
private inductive Op : Ty Unit → Ty Unit → Type
  | equal : Op (.pair .nat .nat) .bool
private def primitives : Primitives base Op where
  execute instruction := match instruction with | .equal => fun value => decide (value.1 = value.2)
  cost _ _ := 1
private def comparison : Expr Op [.nat, .nat] .bool := .op .equal (.pair (.var .here) (.var (.there .here)))
private theorem comparison_correct (lhs rhs : Nat) :
    comparison.denote primitives (lhs, rhs, ()) = decide (lhs = rhs) := rfl
private def counter := Layout.counter 16 256 (by decide) (by decide)
private def cache : CacheLayout 16 Nat Nat where
  key := counter
  value := counter
  capacityPred := 1
  wordFits := by decide
  countFits := by decide
  storageFits := by decide
private def layout : StatefulCacheRead.Layouts 16 Nat Nat (Word 16) where
  cache := cache
  saved := wordRepresentation 16 (by decide)
  storageFits := by decide

-- The fresh routine receives the current runtime state and obtains both a new
-- entry and new state from its oracle. This fixture tests stateful composition,
-- not a cryptographic sampler or a field/group implementation.
private def sampleSpec : OracleSpec (Word 16) := fun _ => counter.Value × Word 16
private def replyView : (Σ _ : Word 16, counter.Value × Word 16) ≃ (Word 16 × (counter.Value × Word 16)) where
  toFun value := (value.1, value.2)
  invFun value := ⟨value.1, value.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
private def port : Interactive.Port 16 sampleSpec where
  Request := Word 16
  source := id
  request := layout.saved
  reply := (layout.saved.prod layout.freshOutput (by decide)).transport replyView
private def source (state : Word 16) : OracleComp sampleSpec (counter.Value × Word 16) := queryBind state Pure.pure
private def project : Realizer .unit port.reply layout.freshOutput Sigma.snd :=
  selectSliceRealizer .unit (by decide) _ _ _ 1 (by decide) (by decide) (fun _ => rfl)
private def draw : Interactive.Code 16 := .seq .query (.compute project.code)
private theorem draw_correct : Interactive.Refines port .unit layout.saved layout.freshOutput source draw := by
  convert (Interactive.Refines.query port .unit).seq (Interactive.Refines.compute port .unit project) using 1
  rfl
private theorem draw_time : Interactive.TimeBound port .unit layout.saved draw 29 :=
  (Interactive.TimeBound.query (port := port) (cost := .unit)).seq (Interactive.Refines.query port .unit)
    (Interactive.TimeBound.compute (port := port) (cost := .unit) project 16 (fun _ => by change 16 ≤ 16; decide))
private theorem draw_words : (draw.lower port).descriptionWords ≤ 117 := by decide
private theorem draw_names : WordIO.NamesBound (draw.lower port) 3 := by constructor <;> decide
private theorem draw_fits : (draw.lower port).DescriptionFits :=
  (.seq (by decide) (WordIO.exchange_descriptionFits 1 3 (by decide) (by decide)) (.compute project.description_fits))

private def code := StatefulCacheRead.code (base := base) (key := .nat) (val := .nat)
  port layout primitives comparison comparison_correct draw
private theorem refined : Interactive.Refines port .unit layout.input layout.output
    (StatefulCacheRead.denote (base := base) (key := .nat) (val := .nat)
      layout primitives comparison comparison_correct source) code :=
  StatefulCacheRead.refines (base := base) (key := .nat) (val := .nat)
    port layout primitives comparison comparison_correct source draw draw_correct
private theorem timed : Interactive.TimeBound port .unit layout.input code
    (StatefulCacheRead.timeBudget (base := base) (key := .nat) (val := .nat) layout 29) :=
  StatefulCacheRead.time_bound (base := base) (key := .nat) (val := .nat)
    port layout primitives comparison comparison_correct draw_correct draw_time
private theorem stored : (code.lower port).descriptionWords ≤
    StatefulCacheRead.codeBudget (base := base) (key := .nat) (val := .nat) layout 117 :=
  StatefulCacheRead.code_bound (base := base) (key := .nat) (val := .nat)
    port layout primitives comparison comparison_correct draw draw_words
private theorem accepted : (code.lower port).DescriptionFits :=
  StatefulCacheRead.descriptionFits (base := base) (key := .nat) (val := .nat)
    port layout primitives comparison comparison_correct draw draw_fits draw_names (by decide)

private theorem valid_iff (key value : Nat) (entries : List (Nat × Nat)) :
    cache.input.valid (key, value, entries, ()) ↔
      (key < 256 ∧ value < 256 ∧ entries.length ≤ 2 ∧ ∀ entry ∈ entries, entry.1 < 256 ∧ entry.2 < 256) ∧
        ((lookupValue key value entries).1 = false → entries.length ≤ 1) := by
  change ((key < 256 ∧ value < 256 ∧ (entries.length ≤ 2 ∧ ∀ entry ∈ entries, entry.1 < 256 ∧ entry.2 < 256) ∧ True) ∧ _) ↔ _
  tauto
private def fullHit : cache.input.Value := ⟨(2, 42, [(1, 7), (2, 0)], ()), by rw [valid_iff]; decide⟩
private def repeated : cache.input.Value := ⟨(2, 42, [(2, 7), (2, 9)], ()), by rw [valid_iff]; decide⟩
private def miss : cache.input.Value := ⟨(2, 42, [(1, 7)], ()), by rw [valid_iff]; decide⟩
example : ¬cache.input.valid (3, 42, [(1, 7), (2, 0)], ()) := by rw [valid_iff]; decide

private def execute (request : cache.input.Value) (state : Word 16) (replies : List (Word 16)) := do
  let initial := layout.input.initial (request, state)
  let before := { initial with
    regs := fun r => if r = 200 then 99 else initial.regs r
    bufs := fun b => if b = 200 then #[77] else initial.bufs b
    caps := fun b => if b = 200 then 4 else initial.caps b
    tapePos := 7 }
  let result ← WordIO.run .unit RandomTape.zero 100000 (code.lower port) before replies
  pure (result.state.bufs 0, result.trace, result.remaining, result.state.bufs 200,
    result.state.caps 200, result.state.regs 200, result.state.tapePos,
    (List.range 20).all (fun i => result.state.caps (i + 1) == 0))

open Lean in
run_cmd do
  unless execute fullHit 11 [] == some (#[0, 2, 1, 7, 2, 0, 11], [], [], #[77], 4, 99, 7, true) do
    throwError "full cache hit sampled or changed the saved state/cached zero"
  unless execute repeated 18 [88] == some (#[7, 2, 2, 7, 2, 9, 18], [], [88], #[77], 4, 99, 7, true) do
    throwError "stateful cache overwrote the first explanation on a duplicate-key hit"
  unless execute miss 11 [11, 9, 12, 88] ==
      some (#[9, 2, 2, 9, 1, 7, 12], [.output 11, .invoke, .input 11, .input 9, .input 12], [88], #[77], 4, 99, 7, true) do
    throwError "cache miss lost its input state, fresh entry, returned state or saved table"
  unless execute miss 18 [18, 0, 25] ==
      some (#[0, 2, 2, 0, 1, 7, 25], [.output 18, .invoke, .input 18, .input 0, .input 25], [], #[77], 4, 99, 7, true) do
    throwError "stateful cache captured a fixed state or rejected a fresh zero entry"
  unless execute miss 11 [] == none do
    throwError "cache miss succeeded without the fresh routine's oracle reply"
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``StatefulCacheRead.refines, ``StatefulCacheRead.denote_value, ``StatefulCacheRead.time_bound,
      ``StatefulCacheRead.code_bound, ``StatefulCacheRead.names, ``StatefulCacheRead.descriptionFits,
      ``StatefulCacheRead.resources, ``CaliperBackend.SchnorrAGM.Cache.model,
      ``CaliperBackend.SchnorrAGM.Cache.freshSource_uniform, ``draw_correct, ``refined, ``timed, ``stored, ``accepted] do
    for dependency in (← collectAxioms name) do
      unless dependency ∈ allowed do throwError "unexpected axiom {dependency} in {name}"

end SignaturesTest.CaliperStatefulCache
