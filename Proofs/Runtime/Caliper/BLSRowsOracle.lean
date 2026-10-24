import Proofs.Runtime.Caliper.BLSRows
import Proofs.Runtime.Caliper.RowFoldStateSource

/-! The executed scalar/pair row loop agrees with the ordered fold using
BLS's original private oracle. The equality includes the final private cache. -/
namespace Signatures.Runtime.CaliperBackend.BLSRows
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat} {Atom : Type} {base : Atom → Type} {key val : Ty Atom} {G : Type}
    [DecidableEq (key.Value base)] [Mul (val.Value base)] [Add (val.Value base)]
    (layout : Layouts w (key.Value base) G (val.Value base))
    (default : layout.accumulation.cache.value.Value)
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    (mul : Implementation .unit layout.accumulation.arithmetic.pair layout.accumulation.cache.value (fun value => value.1 * value.2))
    (add : Implementation .unit layout.accumulation.arithmetic.pair layout.accumulation.cache.value (fun value => value.1 + value.2))
    {slots : Nat} (mulBuffers : mul.program.code.memBound ≤ slots) (reserve : slots + 4 < 2 ^ w)
    (addBuffers : add.program.code.memBound ≤ slots)
    [SampleableType (val.Value base)]
    (source : ProbComp layout.accumulation.cache.value.Value)
    (uniform : Subtype.val <$> source = ($ᵗ (val.Value base) : ProbComp (val.Value base)))

include uniform in
theorem good_privateOracle {capacity : Nat}
    (value : RowFold.Input (base := base) (key := key) (val := val) layout.good capacity)
    (admitted : RowFold.valid (base := base) (key := key) (val := val) layout.good value) :
    Subtype.val <$> goodDenote layout default P comparison correct mul add mulBuffers reserve addBuffers source value =
      ((value.1.val.map Subtype.val).foldlM (fun (accumulator : val.Value base) (row : (key.Value base × G) × val.Value base) => do
        let answer ← (BLS.LazyAGM.Reduction.privateListOracle (M := key.Value base) (R := val.Value base)) (.inr row.1.1)
        pure (accumulator + row.2 * answer)) value.2.val.1).run value.2.val.2 := by
  refine (RowFold.listCache (base := base) (key := key) (val := val) layout.good default P comparison correct
    (BLSPrivateAccumulate.goodUpdate layout.accumulation mul add mulBuffers reserve)
    (BLSPrivateAccumulate.goodUpdate_buffers layout.accumulation mul add mulBuffers reserve addBuffers)
    (BLSPrivateAccumulate.good_reserve layout.accumulation reserve) source value admitted).trans ?_
  change (value.1.val.map Subtype.val).foldlM
    (RowFold.sourceStep (base := base) (key := key) (val := val)
      (combine := fun value => value.2.2 + value.1 * value.2.1) (Subtype.val <$> source)) value.2.val = _
  rw [uniform, RowFold.sourceStep_fold]
  rfl

include uniform in
theorem bad_privateOracle {capacity : Nat}
    (value : RowFold.Input (base := base) (key := key) (val := .pair val val) layout.bad capacity)
    (admitted : RowFold.valid (base := base) (key := key) (val := .pair val val) layout.bad value) :
    Subtype.val <$> badDenote layout default P comparison correct mul add mulBuffers reserve addBuffers source value =
      ((value.1.val.map Subtype.val).foldlM (fun (accumulator : val.Value base × val.Value base) (row : (key.Value base × G) × val.Value base) => do
        let answer ← (BLS.LazyAGM.Reduction.privateListOracle (M := key.Value base) (R := val.Value base × val.Value base)) (.inr row.1.1)
        pure ((accumulator.1 + row.2 * answer.1, accumulator.2 + row.2 * answer.2))) value.2.val.1).run value.2.val.2 := by
  refine (RowFold.listCache (base := base) (key := key) (val := .pair val val) layout.bad (pairDefault layout default) P comparison correct
    (BLSPrivateAccumulate.badUpdate layout.accumulation mul add mulBuffers reserve addBuffers)
    (BLSPrivateAccumulate.badUpdate_buffers layout.accumulation mul add mulBuffers reserve addBuffers)
    (BLSPrivateAccumulate.bad_reserve layout.accumulation reserve)
    (BLSPrivateAccumulate.pairSource layout.accumulation source) value admitted).trans ?_
  have pairLaw := PairSampling.uniform layout.accumulation.cache.value layout.accumulation.cache.value
    layout.accumulation.cache.pairValueFits source source uniform uniform
  change Subtype.val <$> BLSPrivateAccumulate.pairSource layout.accumulation source = _ at pairLaw
  change (value.1.val.map Subtype.val).foldlM
    (RowFold.sourceStep (base := base) (key := key) (val := .pair val val)
      (combine := fun value => (value.2.2.1 + value.1 * value.2.1.1, value.2.2.2 + value.1 * value.2.1.2))
      (Subtype.val <$> BLSPrivateAccumulate.pairSource layout.accumulation source)) value.2.val = _
  rw [pairLaw, RowFold.sourceStep_fold]
  rfl

end Signatures.Runtime.CaliperBackend.BLSRows
