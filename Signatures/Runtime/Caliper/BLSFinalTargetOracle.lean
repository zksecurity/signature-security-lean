import Signatures.Runtime.Caliper.BLSFinalTarget

/-! The final lookup uses the original BLS private oracle, including its
updated cache. The arithmetic is total and introduces no nonzero-denominator
precondition. Pair sampling is derived from the two actual scalar draws. -/
namespace Signatures.Runtime.CaliperBackend.BLSFinalTarget
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat} {Atom : Type} {base : Atom → Type} {key val : Ty Atom}
    [DecidableEq (key.Value base)] [Sub (val.Value base)] [Neg (val.Value base)] [Div (val.Value base)] [SampleableType (val.Value base)]
    (layout : BLSPrivateAccumulate.Layouts w (key.Value base) (val.Value base))
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    (sub : Implementation .unit layout.arithmetic.pair layout.cache.value (fun value => value.1 - value.2))
    (negate : Implementation .unit layout.cache.value layout.cache.value Neg.neg)
    (divide : Implementation .unit layout.arithmetic.pair layout.cache.value (fun value => value.1 / value.2))
    {slots : Nat} (subBuffers : sub.program.code.memBound ≤ slots) (reserve : slots + 4 < 2 ^ w)
    (negBuffers : negate.program.code.memBound ≤ slots) (divBuffers : divide.program.code.memBound ≤ slots)
    (source : ProbComp layout.cache.value.Value)
    (uniform : Subtype.val <$> source = ($ᵗ (val.Value base) : ProbComp (val.Value base)))

include uniform in
omit [Neg (val.Value base)] in
theorem good_privateOracle (value : layout.good.input.Value) :
    Subtype.val <$> goodDenote layout P comparison correct sub divide subBuffers reserve divBuffers source value =
      (fun result => (value.val.2.1 / (result.1 - value.val.2.2), result.2)) <$>
        ((BLS.LazyAGM.Reduction.privateListOracle (M := key.Value base) (R := val.Value base))
          (.inr value.val.1.1)).run value.val.1.2.2.1 :=
  EncodedCacheScalarResult.privateOracle layout.good P comparison correct _ _ _ source uniform value

include uniform in
theorem bad_privateOracle (value : layout.bad.input.Value) :
    Subtype.val <$> badDenote layout P comparison correct sub negate divide subBuffers reserve negBuffers divBuffers source value =
      (fun result => (-(result.1.2 - value.val.2.2.2) / (result.1.1 - value.val.2.2.1), result.2)) <$>
        ((BLS.LazyAGM.Reduction.privateListOracle (M := key.Value base) (R := val.Value base × val.Value base))
          (.inr value.val.1.1)).run value.val.1.2.2.1 :=
  EncodedCacheScalarResult.privateOracle (base := base) (key := key) (val := .pair val val) layout.bad P comparison correct _ _ _
    (BLSPrivateAccumulate.pairSource layout source)
    (PairSampling.uniform layout.cache.value layout.cache.value layout.cache.pairValueFits source source uniform uniform) value
end Signatures.Runtime.CaliperBackend.BLSFinalTarget
