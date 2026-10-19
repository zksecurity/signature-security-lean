import Signatures.Runtime.Caliper.BLSPrivateAccumulate
import Signatures.Runtime.Caliper.CacheAccumulateOracle

/-! The constructed scalar and pair updates use BLS's original private list
oracle. Uniform pair sampling is derived from two scalar draws. -/
namespace Signatures.Runtime.CaliperBackend.BLSPrivateAccumulate
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat} {Atom : Type} {base : Atom → Type} {key val : Ty Atom}
    [DecidableEq (key.Value base)] [Mul (val.Value base)] [Add (val.Value base)] [SampleableType (val.Value base)]
    (layout : Layouts w (key.Value base) (val.Value base))
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    (mul : Implementation .unit layout.arithmetic.pair layout.cache.value (fun value => value.1 * value.2))
    (add : Implementation .unit layout.arithmetic.pair layout.cache.value (fun value => value.1 + value.2))
    {slots : Nat} (mulBuffers : mul.program.code.memBound ≤ slots) (reserve : slots + 4 < 2 ^ w)
    (addBuffers : add.program.code.memBound ≤ slots)
    (source : ProbComp layout.cache.value.Value)
    (uniform : Subtype.val <$> source = ($ᵗ (val.Value base) : ProbComp (val.Value base)))

include uniform in
theorem good_privateOracle (value : layout.good.input.Value) :
    Subtype.val <$> goodDenote layout P comparison correct mul add mulBuffers reserve addBuffers source value =
      (fun result => (value.val.2.2 + value.val.2.1 * result.1, result.2)) <$>
        ((BLS.LazyAGM.Reduction.privateListOracle (M := key.Value base) (R := val.Value base))
          (.inr value.val.1.1)).run value.val.1.2.2.1 :=
  EncodedCacheAccumulate.privateOracle layout.good P comparison correct _ _ _ source uniform value

include uniform in
theorem bad_privateOracle (value : layout.bad.input.Value) :
    Subtype.val <$> badDenote layout P comparison correct mul add mulBuffers reserve addBuffers source value =
      (fun result => ((value.val.2.2.1 + value.val.2.1 * result.1.1,
        value.val.2.2.2 + value.val.2.1 * result.1.2), result.2)) <$>
        ((BLS.LazyAGM.Reduction.privateListOracle (M := key.Value base) (R := val.Value base × val.Value base))
          (.inr value.val.1.1)).run value.val.1.2.2.1 :=
  EncodedCacheAccumulate.privateOracle (base := base) (key := key) (val := .pair val val) layout.bad P comparison correct _ _ _
    (pairSource layout source) (PairSampling.uniform layout.cache.value layout.cache.value layout.cache.pairValueFits source source uniform uniform) value

end Signatures.Runtime.CaliperBackend.BLSPrivateAccumulate
