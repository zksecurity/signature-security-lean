import Signatures.Runtime.Caliper.CacheReadCompilation
import VCVio.OracleComp.QueryTracking.ListCache

/-! The constructed Caliper cache read implements the shared association-list
oracle, preserving the returned value and the complete updated table jointly. -/

namespace Signatures.Runtime.CaliperBackend.EncodedCacheRead

open Caliper BoundedSource OracleComp OracleSpec

private theorem lookup_eq {K V : Type} [DecidableEq K] (key : K) (default : V)
    (entries : List (K × V)) :
    lookupValue key default entries =
      match entries.lookup key with | none => (false, default) | some value => (true, value) := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
    rcases entry with ⟨storedKey, value⟩
    by_cases equal : storedKey = key
    · subst storedKey; simp [lookupValue]
    · have different : (key == storedKey) = false := beq_eq_false_iff_ne.mpr (Ne.symm equal)
      simp [lookupValue, List.lookup_cons, equal, different, ih]

variable {w : Nat} {Atom : Type} {base : Atom → Type} {key val : Ty Atom}
    [DecidableEq (key.Value base)] (layout : CacheLayout w (key.Value base) (val.Value base))
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    {I : Type} {spec : OracleSpec I}

theorem listCache (drawSource : OracleComp spec layout.value.Value) (value : layout.input.Value) :
    Subtype.val <$> denote layout P comparison correct drawSource value =
      (QueryImpl.ListCache.handler (fun _ => Subtype.val <$> drawSource) value.val.1).run value.val.2.2.1 := by
  rw [denote_value]
  have lookupCorrect : (lookupExpr comparison).denote P value.val =
      lookupValue value.val.1 value.val.2.1 value.val.2.2.1 := by
    simpa only [Expr.run_value] using lookupExpr_value P comparison correct value.val.1 value.val.2.1 value.val.2.2.1
  rw [lookupCorrect, lookup_eq]
  cases found : value.val.2.2.1.lookup value.val.1 <;>
    simp [StateT.run, QueryImpl.ListCache.handler, found, Functor.map_map]

theorem observe_listCache (port : Interactive.Port w spec) (drawSource : OracleComp spec layout.value.Value)
    (draw : Interactive.Code w)
    (drawCorrect : Interactive.Refines port .unit layout.lookup.unit.representation layout.value.representation
      (fun _ => drawSource) draw)
    (tape : RandomTape w) (value : layout.input.Value) (before : State w)
    (holds : layout.input.representation.Holds value before) :
    (fun result => Subtype.val <$> Interactive.observe (CacheRead.output layout).representation result) <$>
      (code layout P comparison correct port draw).execute port .unit tape before =
        some <$> (QueryImpl.ListCache.handler (fun _ => Subtype.val <$> drawSource) value.val.1).run value.val.2.2.1 := by
  have observed := (refines layout P comparison correct port drawSource draw drawCorrect).observe tape value before holds
  have mapped := congrArg (fun computation : OracleComp spec (Option (CacheRead.output layout).Value) =>
    (fun result => Subtype.val <$> result) <$> computation) observed
  rw [← listCache layout P comparison correct drawSource value]
  have middle : (fun result => Subtype.val <$> result) <$> some <$> denote layout P comparison correct drawSource value =
      some <$> Subtype.val <$> denote layout P comparison correct drawSource value :=
    (PFunctor.FreeM.comp_map _ _ _).symm.trans
      (PFunctor.FreeM.comp_map (some : (val.Value base × List (key.Value base × val.Value base)) → Option _)
        (Subtype.val : (CacheRead.output layout).Value → _) (denote layout P comparison correct drawSource value))
  exact (PFunctor.FreeM.comp_map _ _ _).trans (mapped.trans middle)

end Signatures.Runtime.CaliperBackend.EncodedCacheRead
