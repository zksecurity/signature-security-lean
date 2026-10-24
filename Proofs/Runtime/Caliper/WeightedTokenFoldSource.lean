import Proofs.Runtime.Caliper.WeightedTokenFold

/-! Streaming extraction preserves the full source cache and the reservation
for later phases. Each message is generated only when its row is evaluated. -/
namespace Signatures.Runtime.CaliperBackend.WeightedTokenFold
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat} {Atom : Type} {base : Atom → Type} {key val : Ty Atom} {M G F : Type}
    [DecidableEq (key.Value base)]
    (layout : WeightedToken.Layouts w (key.Value base) M G F (val.Value base))
    (zero : layout.accumulation.cache.value.Value)
    (terms : Nat) (termCountFits : terms < 2 ^ w)
    (termStorageFits : 1 + terms * (WeightedRows.term layout.accumulation).representation.encoding.words +
      layout.state.representation.encoding.words < 2 ^ w)
    {generate : M → List (key.Value base × F)}
    (generator : Implementation .unit layout.weighted.message
      (GeneratedWeighted.terms layout.accumulation terms termCountFits termStorageFits) generate)
    (default : layout.accumulation.cache.value.Value)
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    {combine : F × (val.Value base × val.Value base) → val.Value base}
    (update : Implementation .unit layout.accumulation.combine layout.accumulation.cache.value combine)
    {slots : Nat} (updateBuffers : update.program.code.memBound ≤ slots) (reserve : slots + 2 < 2 ^ w)
    {I : Type} {spec : OracleSpec I}

theorem fold_cache_growth (source : OracleComp spec layout.accumulation.cache.value.Value)
    (rows : List layout.row.Value) (state : layout.state.Value)
    (admitted : WeightedToken.room layout terms rows.length state) (answer : layout.state.Value)
    (reached : answer ∈ support (rows.foldlM (fun accumulator row =>
      WeightedToken.denote layout zero terms termCountFits termStorageFits generator default
        P comparison correct update updateBuffers reserve source (row, accumulator)) state)) :
    answer.val.2.length ≤ state.val.2.length + terms * rows.length := by
  induction rows generalizing state with
  | nil =>
    simp only [List.foldlM_nil, support_pure, Set.mem_singleton_iff] at reached
    subst answer
    simp
  | cons row rows ih =>
    rw [List.foldlM_cons, mem_support_bind_iff] at reached
    obtain ⟨middle, step, tail⟩ := reached
    have continued := WeightedToken.preserves layout zero terms termCountFits termStorageFits generator default
      P comparison correct update updateBuffers reserve rows.length (row, state) admitted middle step
    have rest := ih middle continued tail
    have ready := WeightedToken.ready_of_room layout terms termCountFits termStorageFits generator rows.length (row, state) admitted
    have first := WeightedToken.cache_growth layout zero terms termCountFits termStorageFits generator default
      P comparison correct update updateBuffers reserve source (row, state) ready middle step
    have bounded := (generator.preserves row.val.1.1 row.property.1.1).1
    change (generate row.val.1.1).length ≤ terms at bounded
    change middle.val.2.length ≤ state.val.2.length + (generate row.val.1.1).length at first
    simp only [List.length_cons, Nat.mul_add, Nat.mul_one]
    omega

theorem cache_growth (source : OracleComp spec layout.accumulation.cache.value.Value) {capacity : Nat}
    (value : Input layout capacity) (admitted : valid layout terms value) (answer : layout.state.Value)
    (reached : answer ∈ support (denote layout zero terms termCountFits termStorageFits generator default
      P comparison correct update updateBuffers reserve source value)) :
    answer.val.2.length ≤ value.2.val.2.length + terms * value.1.val.length :=
  fold_cache_growth layout zero terms termCountFits termStorageFits generator default P comparison correct update updateBuffers reserve
    source value.1.val value.2 admitted answer reached

theorem remaining_room (source : OracleComp spec layout.accumulation.cache.value.Value) {capacity : Nat}
    (value : Input layout capacity) (remaining : Nat)
    (reserved : WeightedToken.room layout terms (value.1.val.length + remaining) value.2)
    (answer : layout.state.Value)
    (reached : answer ∈ support (denote layout zero terms termCountFits termStorageFits generator default
      P comparison correct update updateBuffers reserve source value)) :
    WeightedToken.room layout terms remaining answer := by
  have admitted : valid layout terms value := by
    dsimp only [valid, WeightedToken.room] at *
    rw [Nat.mul_add] at reserved
    omega
  have growth := cache_growth layout zero terms termCountFits termStorageFits generator default
    P comparison correct update updateBuffers reserve source value admitted answer reached
  unfold WeightedToken.room at reserved ⊢
  rw [Nat.mul_add] at reserved
  omega

section Source
variable [Semiring F] [SampleableType (val.Value base)]
    [AddCommMonoid (val.Value base)] [Module F (val.Value base)]
    (combineLaw : ∀ value, combine value = value.2.2 + value.1 • value.2.1)
    (zeroLaw : zero.val = 0)
    (source : ProbComp layout.accumulation.cache.value.Value)
    (uniform : Subtype.val <$> source = ($ᵗ (val.Value base) : ProbComp (val.Value base)))

include combineLaw zeroLaw uniform in
theorem step_source (value : WeightedToken.Input layout) (admitted : WeightedToken.ready layout (generate := generate) value) :
    Subtype.val <$> WeightedToken.denote layout zero terms termCountFits termStorageFits generator default
      P comparison correct update updateBuffers reserve source value =
      WeightedAGM.Batching.cachedStep generate value.2.val value.1.val := by
  rw [WeightedToken.denote, WeightedCoefficient.denote_source layout.weighted zero terms termCountFits termStorageFits generator default
    P comparison correct update updateBuffers reserve combineLaw zeroLaw source uniform _ admitted,
    WeightedAGM.Batching.evalTerms_scale, simulateQ_map, StateT.run_map, Functor.map_map]
  rfl

include combineLaw zeroLaw uniform in
theorem fold_source (rows : List layout.row.Value) (state : layout.state.Value)
    (admitted : WeightedToken.room layout terms rows.length state) :
    Subtype.val <$> rows.foldlM (fun accumulator row =>
      WeightedToken.denote layout zero terms termCountFits termStorageFits generator default
        P comparison correct update updateBuffers reserve source (row, accumulator)) state =
      WeightedAGM.Batching.cached generate (rows.map Subtype.val) state.val := by
  induction rows generalizing state with
  | nil => simp only [List.foldlM_nil, List.map_nil, map_pure, WeightedAGM.Batching.cached]
  | cons row rows ih =>
    have ready := WeightedToken.ready_of_room layout terms termCountFits termStorageFits generator rows.length (row, state) admitted
    have step := step_source layout zero terms termCountFits termStorageFits generator default P comparison correct
      update updateBuffers reserve combineLaw zeroLaw source uniform (row, state) ready
    simp only [WeightedAGM.Batching.cached] at ih ⊢
    rw [List.foldlM_cons, List.map_cons, List.foldlM_cons, map_bind, ← step, bind_map_left]
    apply bind_congr_of_forall_mem_support
    intro answer reached
    exact ih answer (WeightedToken.preserves layout zero terms termCountFits termStorageFits generator default
      P comparison correct update updateBuffers reserve rows.length (row, state) admitted answer reached)

include combineLaw zeroLaw uniform in
theorem listCache {capacity : Nat} (value : Input layout capacity) (admitted : valid layout terms value) :
    Subtype.val <$> denote layout zero terms termCountFits termStorageFits generator default
      P comparison correct update updateBuffers reserve source value =
      WeightedAGM.Batching.cached generate (value.1.val.map Subtype.val) value.2.val :=
  fold_source layout zero terms termCountFits termStorageFits generator default P comparison correct update updateBuffers reserve
    combineLaw zeroLaw source uniform value.1.val value.2 admitted
end Source
end Signatures.Runtime.CaliperBackend.WeightedTokenFold
