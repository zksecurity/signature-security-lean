import Proofs.Runtime.Caliper.BLSCachePairs
import Lean

open Caliper OracleComp OracleSpec Signatures.Runtime Signatures.Runtime.CaliperBackend
open Signatures.Runtime.CaliperBackend.BoundedSource

namespace SignaturesTest.CaliperPairSampling

private def base (_ : Unit) : Type := Fin 2
private instance : SampleableType (Ty.Value base (.atom ())) := inferInstanceAs (SampleableType (Fin 2))
private inductive Op : Ty Unit → Ty Unit → Type
  | equal : Op (.pair .nat .nat) .bool
private def primitives : Primitives base Op where
  execute instruction := match instruction with | .equal => fun value => decide (value.1 = value.2)
  cost _ _ := 1
private def comparison : Expr Op [.nat, .nat] .bool := .op .equal (.pair (.var .here) (.var (.there .here)))
private theorem comparison_correct (left right : Nat) :
    comparison.denote primitives (left, right, ()) = decide (left = right) := rfl

private def layout : CacheLayout 8 Nat (Fin 2) where
  key := Layout.counter 8 256 (by decide) (by decide)
  value := Layout.all (Representation.fin 8 2 (by decide) (by decide))
  capacityPred := 1
  wordFits := by decide
  countFits := by decide
  storageFits := by decide
private theorem pairStorageFits : layout.pairStorageWords < 2 ^ 8 := by decide
private def pairLayout := layout.pairValues pairStorageFits

private def replyView : (Σ _ : layout.lookup.unit.Value, Fin 2) ≃ layout.value.Value where
  toFun packet := ⟨packet.2, trivial⟩
  invFun value := ⟨⟨(), trivial⟩, value.val⟩
  left_inv packet := by rcases packet with ⟨⟨position, valid⟩, answer⟩; cases position; rfl
  right_inv _ := rfl
private def port : Interactive.Port 8 unifSpec where
  Request := layout.lookup.unit.Value
  source _ := 1
  request := layout.lookup.unit.representation
  reply := layout.value.representation.transport replyView
private noncomputable def scalarSource : ProbComp layout.value.Value :=
  (fun value => ⟨value, trivial⟩) <$> ($ᵗ (Fin 2) : ProbComp (Fin 2))
private def scalar : Interactive.Code 8 := .query
private theorem scalar_law : Subtype.val <$> scalarSource = ($ᵗ (Fin 2) : ProbComp (Fin 2)) := by
  simp [scalarSource, Functor.map_map]
private theorem scalar_correct : Interactive.Refines port .unit layout.lookup.unit.representation layout.value.representation
    (fun _ => scalarSource) scalar := by
  have projected := (Interactive.Refines.query port .unit).viewOutput layout.value.representation replyView (fun _ => rfl)
  convert projected using 1 <;> rfl
private theorem scalar_time : Interactive.TimeBound port .unit layout.lookup.unit.representation scalar 4 := Interactive.TimeBound.query
private theorem scalar_words : (scalar.lower port).descriptionWords ≤ 20 := by decide +kernel
private theorem scalar_names : WordIO.NamesBound (scalar.lower port) 3 := by constructor <;> decide +kernel
private theorem scalar_fits : (scalar.lower port).DescriptionFits :=
  WordIO.exchange_descriptionFits (w := 8) 0 1 (by decide) (by decide)

private def pair := PairSampling.code layout.value layout.value layout.wordFits layout.pairValueFits port scalar scalar

private theorem pair_time : Interactive.TimeBound port .unit layout.lookup.unit.representation pair 44 :=
  PairSampling.time_bound (hw := layout.wordFits) (fits := layout.pairValueFits) scalar_correct scalar_correct scalar_time scalar_time
example : (pair.lower port).descriptionWords ≤ 215 :=
  PairSampling.code_bound layout.value layout.value layout.wordFits layout.pairValueFits port scalar scalar scalar_words scalar_words
example : WordIO.NamesBound (pair.lower port) 4 :=
  PairSampling.names layout.value layout.value layout.wordFits layout.pairValueFits port scalar scalar scalar_names scalar_names
example : (pair.lower port).DescriptionFits :=
  PairSampling.descriptionFits layout.value layout.value layout.wordFits layout.pairValueFits port scalar scalar
    scalar_fits scalar_fits scalar_names (by decide)
example : (pair.lower port).staticWords 201 201 ≤ 1035 :=
  PairSampling.staticMemory layout.value layout.value layout.wordFits layout.pairValueFits port scalar scalar
    scalar_words scalar_words scalar_names scalar_names 201 201
example : Subtype.val <$> PairSampling.denote layout.value layout.value layout.pairValueFits scalarSource scalarSource =
    ($ᵗ (Fin 2 × Fin 2) : ProbComp (Fin 2 × Fin 2)) :=
  PairSampling.uniform layout.value layout.value layout.pairValueFits scalarSource scalarSource scalar_law scalar_law

private def runCode (program : Interactive.Code 8) (replies : List (Word 8)) := do
  let initial := layout.lookup.unit.representation.initial ⟨(), trivial⟩
  let before := { initial with
    regs := fun register => if register = 200 then 99 else initial.regs register
    bufs := fun buffer => if buffer = 200 then #[77] else initial.bufs buffer
    caps := fun buffer => if buffer = 200 then 1 else initial.caps buffer
    tapePos := 7 }
  let result ← WordIO.run .unit RandomTape.zero 1000 (program.lower port) before replies
  pure ((result.state.bufs 0, result.state.bufs 200, result.state.regs 200, result.state.tapePos), result.trace, result.remaining)

private def runPair := runCode pair

-- Different replies detect accidental reuse and reversed output order.
example : runPair [1, 0, 1] = some ((#[1, 0], #[77], 99, 7), [.invoke, .input 1, .invoke, .input 0], [1]) := by decide +kernel
example : runPair [0, 1] = some ((#[0, 1], #[77], 99, 7), [.invoke, .input 0, .invoke, .input 1], []) := by decide +kernel
example : runPair [1] = none := by decide +kernel

-- The second callee may use buffer 2. Retention must reserve a different name.
private def scratchSecond : Interactive.Code 8 := .seq (.compute (.memFree 2)) scalar
example : runCode (PairSampling.code layout.value layout.value layout.wordFits layout.pairValueFits port scalar scratchSecond) [1, 0] =
    some ((#[1, 0], #[77], 99, 7), [.invoke, .input 1, .invoke, .input 0], []) := by decide +kernel

private def cache := BLSCache.pairCode (base := base) (key := .nat) (val := .atom ())
  layout pairStorageFits primitives comparison comparison_correct port scalar

example : Interactive.TimeBound port .unit pairLayout.input.representation cache
    (EncodedCacheRead.timeBudget (base := base) (key := .nat) (val := .pair (.atom ()) (.atom ())) pairLayout 44) :=
  BLSCache.pair_time (base := base) (key := .nat) (val := .atom ()) layout pairStorageFits primitives comparison comparison_correct
    port scalar scalar_correct scalar_time
example : (cache.lower port).DescriptionFits :=
  BLSCache.pair_descriptionFits (base := base) (key := .nat) (val := .atom ()) layout pairStorageFits primitives comparison comparison_correct
    port scalar scalar_fits scalar_names (by decide)

private theorem valid_iff (key : Nat) (value : Fin 2 × Fin 2) (entries : List (Nat × (Fin 2 × Fin 2))) :
    pairLayout.input.valid (key, value, entries, ()) ↔
      key < 256 ∧ entries.length ≤ 2 ∧ (∀ entry ∈ entries, entry.1 < 256) ∧
      ((lookupValue key value entries).1 = false → entries.length ≤ 1) := by
  change ((key < 256 ∧ (True ∧ True) ∧ (entries.length ≤ 2 ∧ ∀ entry ∈ entries, entry.1 < 256 ∧ True ∧ True) ∧ True) ∧ _) ↔ _
  simp only [true_and, and_true]
  tauto

private def empty : pairLayout.input.Value := ⟨(2, (0, 0), [], ()), by rw [valid_iff]; decide⟩
private def fullHit : pairLayout.input.Value := ⟨(1, (0, 0), [(1, (1, 0)), (2, (0, 1))], ()), by rw [valid_iff]; decide⟩
private def runCache (value : pairLayout.input.Value) (replies : List (Word 8)) := do
  let result ← WordIO.run .unit RandomTape.zero 40000 (cache.lower port) (pairLayout.input.representation.initial value) replies
  pure (result.state.bufs 0, result.trace, result.remaining)

-- A miss performs both scalar draws; a full-table hit performs neither.
example : runCache empty [1, 0, 1] = some (#[1, 0, 1, 2, 1, 0, 0, 0, 0], [.invoke, .input 1, .invoke, .input 0], [1]) := by decide +kernel
example : runCache fullHit [0, 1] = some (#[1, 0, 2, 1, 1, 0, 2, 0, 1], [], [0, 1]) := by decide +kernel

example (tape : RandomTape 8) (value : pairLayout.input.Value) :
    (fun result => Subtype.val <$> Interactive.observe (CacheRead.output pairLayout).representation result) <$>
      cache.execute port .unit tape (pairLayout.input.representation.initial value) =
        some <$> ((BLS.LazyAGM.Reduction.privateListOracle (M := Nat) (R := Fin 2 × Fin 2)) (.inr value.val.1)).run value.val.2.2.1 :=
  BLSCache.pair_observe (base := base) (key := .nat) (val := .atom ()) layout pairStorageFits primitives comparison comparison_correct
    port scalar scalarSource scalar_correct scalar_law tape value _ (pairLayout.input.representation.initial_holds value)

open Lean in
run_cmd do
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``PairSampling.refines, ``PairSampling.uniform, ``PairSampling.retained_time, ``PairSampling.time_bound,
      ``PairSampling.code_bound, ``PairSampling.names, ``PairSampling.descriptionFits, ``PairSampling.staticMemory, ``PairSampling.memoryBound,
      ``CacheLayout.pairValueFits, ``BLSCache.pair_time, ``BLSCache.pair_words, ``BLSCache.pair_descriptionFits,
      ``BLSCache.pair_observe, ``scalar_correct, ``scalar_law, ``pair_time] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"

end SignaturesTest.CaliperPairSampling
