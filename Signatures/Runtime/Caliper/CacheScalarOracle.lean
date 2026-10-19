import Signatures.Runtime.Caliper.CacheScalarMemory
import Signatures.Runtime.Caliper.BLSCache

/-! Observing the executed cache/update yields the joint source result. The
uniform law specializes the same code to BLS's private oracle. -/
namespace Signatures.Runtime.CaliperBackend.EncodedCacheScalarResult
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat} {Atom : Type} {base : Atom → Type} {key val : Ty Atom} {F : Type}
    [DecidableEq (key.Value base)] (layout : CacheAccumulate.Layouts w (key.Value base) F (val.Value base))
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    {combine : F × (val.Value base × val.Value base) → F}
    (update : Implementation .unit layout.combine layout.coefficient combine)
    {slots : Nat} (updateBuffers : update.program.code.memBound ≤ slots) (reserve : slots + 2 < 2 ^ w)
    {I : Type} {spec : OracleSpec I}

theorem observe_listCache (port : Interactive.Port w spec) (drawSource : OracleComp spec layout.cache.value.Value)
    (draw : Interactive.Code w)
    (drawCorrect : Interactive.Refines port .unit layout.cache.lookup.unit.representation layout.cache.value.representation
      (fun _ => drawSource) draw)
    (tape : RandomTape w) (value : layout.input.Value) (before : State w)
    (holds : layout.input.representation.Holds value before) :
    (fun result => Subtype.val <$> Interactive.observe (CacheScalarResult.output layout).representation result) <$>
      (code layout P comparison correct update updateBuffers reserve port draw).execute port .unit tape before =
        some <$> ((fun result => (combine (value.val.2.1, result.1, value.val.2.2), result.2)) <$>
          (QueryImpl.ListCache.handler (fun _ => Subtype.val <$> drawSource) value.val.1.1).run value.val.1.2.2.1) := by
  have observed := (refines layout P comparison correct update updateBuffers reserve port drawSource draw drawCorrect).observe tape value before holds
  have mapped := congrArg (fun computation : OracleComp spec (Option (CacheScalarResult.output layout).Value) =>
    (fun result => Subtype.val <$> result) <$> computation) observed
  rw [← listCache layout P comparison correct update updateBuffers reserve drawSource value]
  have middle : (fun result => Subtype.val <$> result) <$> some <$>
      denote layout P comparison correct update updateBuffers reserve drawSource value =
    some <$> Subtype.val <$> denote layout P comparison correct update updateBuffers reserve drawSource value :=
    (PFunctor.FreeM.comp_map _ _ _).symm.trans
      (PFunctor.FreeM.comp_map (some : (F × List (key.Value base × val.Value base)) → Option _)
        (Subtype.val : (CacheScalarResult.output layout).Value → _) _)
  exact (PFunctor.FreeM.comp_map _ _ _).trans (mapped.trans middle)

theorem privateOracle [SampleableType (val.Value base)] (drawSource : ProbComp layout.cache.value.Value)
    (drawLaw : Subtype.val <$> drawSource = ($ᵗ (val.Value base) : ProbComp (val.Value base))) (value : layout.input.Value) :
    Subtype.val <$> denote layout P comparison correct update updateBuffers reserve drawSource value =
      (fun result => (combine (value.val.2.1, result.1, value.val.2.2), result.2)) <$>
        ((BLS.LazyAGM.Reduction.privateListOracle (M := key.Value base) (R := val.Value base))
          (.inr value.val.1.1)).run value.val.1.2.2.1 := by
  rw [listCache, BLS.LazyAGM.Reduction.privateListOracle_lookup]
  simp only [StateT.run, QueryImpl.ListCache.handler, drawLaw]
  rfl

theorem cache_growth (drawSource : OracleComp spec layout.cache.value.Value) (value : layout.input.Value)
    (answer : (CacheScalarResult.output layout).Value)
    (reached : answer ∈ support (denote layout P comparison correct update updateBuffers reserve drawSource value)) :
    answer.val.2.length ≤ value.val.1.2.2.1.length + 1 := by
  have erased : answer.val ∈ support (Subtype.val <$> denote layout P comparison correct update updateBuffers reserve drawSource value) := by
    rw [support_map]
    exact ⟨answer, reached, rfl⟩
  rw [listCache] at erased
  cases found : value.val.1.2.2.1.lookup value.val.1.1 with
  | none =>
    simp only [StateT.run, QueryImpl.ListCache.handler, found, Functor.map_map, support_map, Set.mem_image] at erased
    obtain ⟨fresh, _, equal⟩ := erased
    have lengths := congrArg (fun result => result.2.length) equal
    simp only [List.length_cons] at lengths
    omega
  | some cached =>
    simp only [StateT.run, QueryImpl.ListCache.handler, found, map_pure, support_pure, Set.mem_singleton_iff] at erased
    have lengths := congrArg (fun result => result.2.length) erased
    change answer.val.2.length = value.val.1.2.2.1.length at lengths
    omega

end Signatures.Runtime.CaliperBackend.EncodedCacheScalarResult
