import Proofs.Runtime.Caliper.CacheReadOracle
import Proofs.BLS.LazyAGMList

/-! The actual Caliper cache code implements the private list oracle used by
both lazy BLS AGM reductions. The value type may be a scalar or a scalar pair.
The primitive draw's uniform-sampling law remains an explicit premise. -/

namespace Signatures.Runtime.CaliperBackend.BLSCache

open Caliper BoundedSource OracleComp OracleSpec

variable {w : Nat} {Atom : Type} {base : Atom → Type} {key val : Ty Atom}
    [DecidableEq (key.Value base)] [SampleableType (val.Value base)]
    (layout : CacheLayout w (key.Value base) (val.Value base))
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))

theorem denote_privateOracle (drawSource : ProbComp layout.value.Value)
    (drawLaw : Subtype.val <$> drawSource = ($ᵗ (val.Value base) : ProbComp (val.Value base)))
    (value : layout.input.Value) :
    Subtype.val <$> EncodedCacheRead.denote layout P comparison correct drawSource value =
      ((BLS.LazyAGM.Reduction.privateListOracle (M := key.Value base) (R := val.Value base))
        (.inr value.val.1)).run value.val.2.2.1 := by
  rw [EncodedCacheRead.listCache, BLS.LazyAGM.Reduction.privateListOracle_lookup]
  simp only [StateT.run, QueryImpl.ListCache.handler, drawLaw]
  rfl

/-- This is the same word program and source refinement as the generic cache
read, so all its proved time, code and memory bounds apply without an adapter. -/
theorem observe_privateOracle (port : Interactive.Port w unifSpec)
    (drawSource : ProbComp layout.value.Value) (draw : Interactive.Code w)
    (drawCorrect : Interactive.Refines port .unit layout.lookup.unit.representation layout.value.representation
      (fun _ => drawSource) draw)
    (drawLaw : Subtype.val <$> drawSource = ($ᵗ (val.Value base) : ProbComp (val.Value base)))
    (tape : RandomTape w) (value : layout.input.Value) (before : State w)
    (holds : layout.input.representation.Holds value before) :
    (fun result => Subtype.val <$> Interactive.observe (CacheRead.output layout).representation result) <$>
      (EncodedCacheRead.code layout P comparison correct port draw).execute port .unit tape before =
        some <$> ((BLS.LazyAGM.Reduction.privateListOracle (M := key.Value base) (R := val.Value base))
          (.inr value.val.1)).run value.val.2.2.1 := by
  rw [EncodedCacheRead.observe_listCache layout P comparison correct port drawSource draw drawCorrect tape value before holds]
  have source := denote_privateOracle layout P comparison correct drawSource drawLaw value
  rw [EncodedCacheRead.listCache] at source
  exact congrArg (fun computation : ProbComp (val.Value base × List (key.Value base × val.Value base)) => some <$> computation) source

end Signatures.Runtime.CaliperBackend.BLSCache
