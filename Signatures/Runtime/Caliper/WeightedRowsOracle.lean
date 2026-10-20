import Signatures.Runtime.Caliper.WeightedRows
import Signatures.Runtime.WeightedEvaluateSource
import Signatures.BLS.Spec.LazyAGMList

/-! The executed weighted fold is the source game's `evalTerms`, including
its final private cache. The starting accumulator may be nonzero, which also
supports streaming extraction across several generated term lists. -/
namespace Signatures.Runtime.CaliperBackend.WeightedRows
open Caliper BoundedSource OracleComp OracleSpec Model.LazyAGM
open BLS.LazyAGM.Reduction (privateListOracle)

section Fold
variable {Atom : Type} {base : Atom → Type} {key val : Ty Atom} {F I : Type}
    [DecidableEq (key.Value base)] {spec : OracleSpec I}
    (combine : F × (val.Value base × val.Value base) → val.Value base)

theorem sourceStep_fold (sample : OracleComp spec (val.Value base))
    (entries : List (key.Value base × F)) (accumulator : val.Value base)
    (cache : List (key.Value base × val.Value base)) :
    entries.foldlM (sourceStep (combine := combine) sample) (accumulator, cache) =
      (entries.foldlM (fun (accumulator : val.Value base) (entry : key.Value base × F) => do
        let answer ← QueryImpl.ListCache.handler (fun _ => sample) entry.1
        pure (combine (entry.2, answer, accumulator))) accumulator).run cache := by
  induction entries generalizing accumulator cache with
  | nil => rfl
  | cons entry entries ih =>
    simp only [List.foldlM_cons, sourceStep, bind_map_left, StateT.run_bind, bind_assoc, pure_bind]
    congr 1
    funext answer
    exact ih (combine (entry.2, answer.1, accumulator)) answer.2

variable [SampleableType (val.Value base)] [AddCommMonoid (val.Value base)] [SMul F (val.Value base)]
    (combineLaw : ∀ value, combine value = value.2.2 + value.1 • value.2.1)

include combineLaw in
theorem sourceStep_evalTerms (entries : List (key.Value base × F)) (accumulator : val.Value base)
    (cache : List (key.Value base × val.Value base)) :
    entries.foldlM (sourceStep (combine := combine) ($ᵗ (val.Value base))) (accumulator, cache) =
      (fun result => (accumulator + result.1, result.2)) <$>
        (simulateQ (privateListOracle (M := key.Value base) (R := val.Value base)) (evalTerms entries)).run cache := by
  rw [sourceStep_fold]
  simp_rw [combineLaw]
  have source := WeightedAGM.Evaluate.foldTerms_simulate
    (privateListOracle (M := key.Value base) (R := val.Value base)) entries accumulator
  have projected := congrArg (fun action : StateT (List (key.Value base × val.Value base)) ProbComp (val.Value base) =>
    action.run cache) source
  simp only [StateT.run_map] at projected
  exact projected
end Fold

variable {w : Nat} {Atom : Type} {base : Atom → Type} {key val : Ty Atom} {F : Type}
    [DecidableEq (key.Value base)] [SampleableType (val.Value base)]
    [AddCommMonoid (val.Value base)] [SMul F (val.Value base)]
    (layout : CacheAccumulate.Layouts w (key.Value base) F (val.Value base))
    (default : layout.cache.value.Value)
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    {combine : F × (val.Value base × val.Value base) → val.Value base}
    (update : Implementation .unit layout.combine layout.cache.value combine)
    {slots : Nat} (updateBuffers : update.program.code.memBound ≤ slots) (reserve : slots + 2 < 2 ^ w)
    (combineLaw : ∀ value, combine value = value.2.2 + value.1 • value.2.1)
    (source : ProbComp layout.cache.value.Value)
    (uniform : Subtype.val <$> source = ($ᵗ (val.Value base) : ProbComp (val.Value base)))

include combineLaw uniform in
theorem evalTerms_source {capacity : Nat} (value : Input layout capacity) (admitted : valid layout value) :
    Subtype.val <$> denote layout default P comparison correct update updateBuffers reserve source value =
      (fun result => (value.2.val.1 + result.1, result.2)) <$>
        (simulateQ (privateListOracle (M := key.Value base) (R := val.Value base))
          (evalTerms (value.1.val.map Subtype.val))).run value.2.val.2 := by
  rw [listCache layout default P comparison correct update updateBuffers reserve source value admitted, uniform]
  exact sourceStep_evalTerms combine combineLaw _ _ _

end Signatures.Runtime.CaliperBackend.WeightedRows
