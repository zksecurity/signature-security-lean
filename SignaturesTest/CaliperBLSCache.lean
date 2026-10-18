import Signatures.Runtime.Caliper.BLSCache
import Signatures.Runtime.Caliper.BLSCacheReachability
import Lean

open Caliper OracleComp OracleSpec Signatures.Runtime Signatures.Runtime.CaliperBackend
open Signatures.Runtime.CaliperBackend.BoundedSource Model.LazyAGM BLS.LazyAGM.Reduction

namespace SignaturesTest.CaliperBLSCache

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

-- The key domain is infinite. Only messages actually used by this client fit.
private def layout : CacheLayout 8 Nat (Fin 2) where
  key := Layout.counter 8 256 (by decide) (by decide)
  value := Layout.all (Representation.fin 8 2 (by decide) (by decide))
  capacityPred := 1
  wordFits := by decide
  countFits := by decide
  storageFits := by decide

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
private noncomputable def drawSource : ProbComp layout.value.Value :=
  (fun value => ⟨value, trivial⟩) <$> ($ᵗ (Fin 2) : ProbComp (Fin 2))
private def draw : Interactive.Code 8 := .query

-- This law is for the ideal uniform-query interface, not a fair-bit tape sampler.
private theorem draw_law : Subtype.val <$> drawSource = ($ᵗ (Fin 2) : ProbComp (Fin 2)) := by
  simp [drawSource, Functor.map_map]
private theorem draw_correct : Interactive.Refines port .unit layout.lookup.unit.representation layout.value.representation
    (fun _ => drawSource) draw := by
  have projected := (Interactive.Refines.query port .unit).viewOutput layout.value.representation replyView (fun _ => rfl)
  convert projected using 1 <;> rfl

private def program := EncodedCacheRead.code (base := base) (key := .nat) (val := .atom ())
  layout primitives comparison comparison_correct port draw

example (tape : RandomTape 8) (value : layout.input.Value) :
    (fun result => Subtype.val <$> Interactive.observe (CacheRead.output layout).representation result) <$>
      program.execute port .unit tape (layout.input.representation.initial value) =
        some <$> ((privateListOracle (M := Nat) (R := Fin 2)) (.inr value.val.1)).run value.val.2.2.1 :=
  BLSCache.observe_privateOracle (base := base) (key := .nat) (val := .atom ())
    layout primitives comparison comparison_correct port drawSource draw draw_correct draw_law tape value _
    (layout.input.representation.initial_holds value)

private def nextKey (value : Fin 2) : Nat := if value = 0 then 0 else 1
private def tail (value : Fin 2) : OracleComp (baseSpec Nat (Fin 2)) (Fin 2) :=
  queryBind (.inr (nextKey value)) Pure.pure
private def adaptive : OracleComp (baseSpec Nat (Fin 2)) (Fin 2) := queryBind (.inr 0) tail

private theorem adaptive_queries : AllQueriesSatisfy adaptive (BLSCache.allowedQuery layout) := by
  change (0 < 256) ∧ ∀ value : Fin 2, (nextKey value < 256) ∧ ∀ _ : Fin 2, True
  refine ⟨by decide, fun value => ⟨?_, fun _ => trivial⟩⟩
  unfold nextKey
  split <;> decide
private theorem adaptive_bound : IsTotalQueryBound adaptive 2 := by
  change (0 < 2) ∧ ∀ _ : Fin 2, (0 < 1) ∧ ∀ _ : Fin 2, True
  exact ⟨by decide, fun _ => ⟨by decide, fun _ => trivial⟩⟩

private theorem firstPath (value : Fin 2) :
    SourcePrefix privateListOracle adaptive [] (tail value) [(0, value)] 1 := by
  apply SourcePrefix.step (handler := privateListOracle (M := Nat) (R := Fin 2))
    (query := .inr 0) (next := tail) SourcePrefix.start (value, [(0, value)])
  rw [privateListOracle_lookup]
  simp only [List.lookup_nil, support_map, Set.mem_image]
  exact ⟨value, mem_support_uniformSample (Fin 2), rfl⟩

private theorem ready (value : Fin 2) : layout.input.valid (nextKey value, 0, [(0, value)], ()) :=
  BLSCache.ready layout (fun _ _ => trivial) adaptive_queries (by simp [BLSCache.entriesFit])
    adaptive_bound (by decide) (nextKey value) Pure.pure (firstPath value) 0 trivial

-- Execute both continuations of the same adaptive source: a hit after zero,
-- and a fresh second key after one. Both use the unchanged two-entry layout.
private def runTail (value : Fin 2) (replies : List (Word 8)) := do
  let represented : layout.input.Value := ⟨(nextKey value, 0, [(0, value)], ()), ready value⟩
  let result ← WordIO.run .unit RandomTape.zero 30000 (program.lower port)
    (layout.input.representation.initial represented) replies
  pure (result.state.bufs 0, result.trace, result.remaining)

example : runTail 0 [1] = some (#[0, 1, 0, 0, 0, 0], [], [1]) := by decide +kernel
example : runTail 1 [0, 1] = some (#[0, 2, 1, 0, 0, 1], [.invoke, .input 0], [1]) := by decide +kernel
example : ¬ BLSCache.allowedQuery layout (.inr 256) := by change ¬(256 < 256); decide
example : ¬ layout.input.valid (2, 0, [(0, 0), (1, 1)], ()) := by
  intro valid
  have room := valid.2 (by decide +kernel)
  change 2 ≤ 1 at room
  omega

open Lean in
run_cmd do
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``SourcePrefix.append, ``SourcePrefix.complete, ``SourcePrefix.queryBound, ``SourcePrefix.allowed, ``SourcePrefix.growth,
      ``EncodedCacheRead.listCache, ``EncodedCacheRead.observe_listCache,
      ``BLSCache.denote_privateOracle, ``BLSCache.observe_privateOracle,
      ``BLSCache.query_entries, ``BLSCache.prefix_entries, ``BLSCache.ready,
      ``BLSCache.good_ready, ``BLSCache.bad_ready, ``draw_law, ``draw_correct, ``ready] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"

end SignaturesTest.CaliperBLSCache
