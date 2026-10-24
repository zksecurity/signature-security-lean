import Proofs.Runtime.Caliper.BLSExtractArithmeticNames
import Proofs.Runtime.Caliper.BLSPrivateAccumulate
import Proofs.Runtime.Caliper.CacheScalarOracle

/-! The final BLS private lookup and extraction arithmetic. The good frame
already contains beta + hashes and the signature sum; the bad frame contains
beta and the signature pair. Construction of that incoming frame is a separate
phase. Here the lookup, retained copies, scalar arithmetic and final cache all
belong to the same executed program. -/
namespace Signatures.Runtime.CaliperBackend.BLSFinalTarget
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat} {Atom : Type} {base : Atom → Type} {key val : Ty Atom}
    [DecidableEq (key.Value base)] [Sub (val.Value base)] [Neg (val.Value base)] [Div (val.Value base)]
    (layout : BLSPrivateAccumulate.Layouts w (key.Value base) (val.Value base))
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    (sub : Implementation .unit layout.arithmetic.pair layout.cache.value (fun value => value.1 - value.2))
    (negate : Implementation .unit layout.cache.value layout.cache.value Neg.neg)
    (divide : Implementation .unit layout.arithmetic.pair layout.cache.value (fun value => value.1 / value.2))
    {slots : Nat} (subBuffers : sub.program.code.memBound ≤ slots) (reserve : slots + 4 < 2 ^ w)
    (negBuffers : negate.program.code.memBound ≤ slots) (divBuffers : divide.program.code.memBound ≤ slots)

def goodUpdate : Implementation .unit layout.good.combine layout.good.coefficient
    (fun value => value.1 / (value.2.1 - value.2.2)) :=
  BLSExtractArithmetic.good layout.arithmetic sub subBuffers
    (Nat.lt_of_le_of_lt (Nat.add_le_add_left (by decide : 2 ≤ 4) slots) reserve) divide
def badUpdate : Implementation .unit layout.bad.combine layout.bad.coefficient
    (fun value => -(value.2.1.2 - value.2.2.2) / (value.2.1.1 - value.2.2.1)) :=
  BLSExtractArithmetic.bad layout.arithmetic sub subBuffers
    (Nat.lt_of_le_of_lt (Nat.add_le_add_left (by decide : 2 ≤ 4) slots) reserve) negate negBuffers divide
include divBuffers in
omit [DecidableEq (key.Value base)] [Neg (val.Value base)] in
theorem goodUpdate_buffers : (goodUpdate layout sub divide subBuffers reserve).program.code.memBound ≤ max 2 slots + 1 :=
  BLSExtractArithmetic.good_buffers layout.arithmetic sub subBuffers _ divide divBuffers
include divBuffers in
omit [DecidableEq (key.Value base)] in
theorem badUpdate_buffers : (badUpdate layout sub negate divide subBuffers reserve negBuffers).program.code.memBound ≤ max 3 slots + 1 :=
  BLSExtractArithmetic.bad_buffers layout.arithmetic sub subBuffers _ negate negBuffers divide divBuffers
include layout reserve in
omit [DecidableEq (key.Value base)] [Sub (val.Value base)] [Neg (val.Value base)] [Div (val.Value base)] in
theorem good_reserve : (max 2 slots + 1) + 2 < 2 ^ w := by have := layout.cache.wordFits; omega
include layout reserve in
omit [DecidableEq (key.Value base)] [Sub (val.Value base)] [Neg (val.Value base)] [Div (val.Value base)] in
theorem bad_reserve : (max 3 slots + 1) + 2 < 2 ^ w := by have := layout.cache.wordFits; omega

variable {I : Type} {spec : OracleSpec I}
def goodCode (port : Interactive.Port w spec) (scalar : Interactive.Code w) : Interactive.Code w :=
  EncodedCacheScalarResult.code layout.good P comparison correct (goodUpdate layout sub divide subBuffers reserve)
    (goodUpdate_buffers layout sub divide subBuffers reserve divBuffers) (good_reserve layout reserve) port scalar
def badCode (port : Interactive.Port w spec) (scalar : Interactive.Code w) : Interactive.Code w :=
  EncodedCacheScalarResult.code (base := base) (key := key) (val := .pair val val) layout.bad P comparison correct
    (badUpdate layout sub negate divide subBuffers reserve negBuffers)
    (badUpdate_buffers layout sub negate divide subBuffers reserve negBuffers divBuffers) (bad_reserve layout reserve) port
    (BLSPrivateAccumulate.pairSampler layout port scalar)
def goodDenote (source : OracleComp spec layout.cache.value.Value) :
    layout.good.input.Value → OracleComp spec (CacheScalarResult.output layout.good).Value :=
  EncodedCacheScalarResult.denote layout.good P comparison correct (goodUpdate layout sub divide subBuffers reserve)
    (goodUpdate_buffers layout sub divide subBuffers reserve divBuffers) (good_reserve layout reserve) source
def badDenote (source : OracleComp spec layout.cache.value.Value) :
    layout.bad.input.Value → OracleComp spec (CacheScalarResult.output layout.bad).Value :=
  EncodedCacheScalarResult.denote (base := base) (key := key) (val := .pair val val) layout.bad P comparison correct
    (badUpdate layout sub negate divide subBuffers reserve negBuffers)
    (badUpdate_buffers layout sub negate divide subBuffers reserve negBuffers divBuffers) (bad_reserve layout reserve)
    (BLSPrivateAccumulate.pairSource layout source)

variable (port : Interactive.Port w spec) {source : OracleComp spec layout.cache.value.Value} {scalar : Interactive.Code w}
    (scalarCorrect : Interactive.Refines port .unit layout.cache.lookup.unit.representation layout.cache.value.representation
      (fun _ => source) scalar)
include scalarCorrect in
omit [Neg (val.Value base)] in
theorem good_refines : Interactive.Refines port .unit layout.good.input.representation (CacheScalarResult.output layout.good).representation
    (goodDenote layout P comparison correct sub divide subBuffers reserve divBuffers source)
    (goodCode layout P comparison correct sub divide subBuffers reserve divBuffers port scalar) :=
  EncodedCacheScalarResult.refines layout.good P comparison correct _ _ _ port source scalar scalarCorrect
include scalarCorrect in
theorem bad_refines : Interactive.Refines port .unit layout.bad.input.representation (CacheScalarResult.output layout.bad).representation
    (badDenote layout P comparison correct sub negate divide subBuffers reserve negBuffers divBuffers source)
    (badCode layout P comparison correct sub negate divide subBuffers reserve negBuffers divBuffers port scalar) :=
  EncodedCacheScalarResult.refines (base := base) (key := key) (val := .pair val val) layout.bad P comparison correct _ _ _ port
    (BLSPrivateAccumulate.pairSource layout source) (BLSPrivateAccumulate.pairSampler layout port scalar)
    (PairSampling.refines (hw := layout.cache.wordFits) (fits := layout.cache.pairValueFits) scalarCorrect scalarCorrect)

variable {scalarTime scalarWords subTime subWords negTime negWords divTime divWords : Nat}
    (scalarTimeBound : Interactive.TimeBound port .unit layout.cache.lookup.unit.representation scalar scalarTime)
    (scalarWordsBound : (scalar.lower port).descriptionWords ≤ scalarWords)
    (subBound : sub.BoundedBy subTime subWords) (negBound : negate.BoundedBy negTime negWords) (divBound : divide.BoundedBy divTime divWords)
include scalarCorrect scalarTimeBound subBound divBound in
omit [Neg (val.Value base)] in
theorem good_time : Interactive.TimeBound port .unit layout.good.input.representation
    (goodCode layout P comparison correct sub divide subBuffers reserve divBuffers port scalar)
    (EncodedCacheScalarResult.timeBudget layout.good scalarTime (BLSExtractArithmetic.goodTime layout.arithmetic subTime divTime)) :=
  EncodedCacheScalarResult.time_bound layout.good P comparison correct _ _ _ port scalarCorrect scalarTimeBound
    (BLSExtractArithmetic.good_bounded layout.arithmetic sub subBound subBuffers _ divide divBound)
include scalarCorrect scalarTimeBound subBound negBound divBound in
theorem bad_time : Interactive.TimeBound port .unit layout.bad.input.representation
    (badCode layout P comparison correct sub negate divide subBuffers reserve negBuffers divBuffers port scalar)
    (EncodedCacheScalarResult.timeBudget (base := base) (key := key) (val := .pair val val) layout.bad
      (PairSampling.timeBudget layout.cache.value layout.cache.value scalarTime scalarTime)
      (BLSExtractArithmetic.badTime layout.arithmetic subTime negTime divTime)) :=
  EncodedCacheScalarResult.time_bound (base := base) (key := key) (val := .pair val val) layout.bad P comparison correct _ _ _ port
    (PairSampling.refines (hw := layout.cache.wordFits) (fits := layout.cache.pairValueFits) scalarCorrect scalarCorrect)
    (PairSampling.time_bound (hw := layout.cache.wordFits) (fits := layout.cache.pairValueFits) scalarCorrect scalarCorrect scalarTimeBound scalarTimeBound)
    (BLSExtractArithmetic.bad_bounded layout.arithmetic sub subBound subBuffers _ negate negBound negBuffers divide divBound)
include scalarWordsBound subBound divBound in
omit [Neg (val.Value base)] in
theorem good_words : ((goodCode layout P comparison correct sub divide subBuffers reserve divBuffers port scalar).lower port).descriptionWords ≤
    EncodedCacheScalarResult.codeBudget layout.good scalarWords (BLSExtractArithmetic.goodCode layout.arithmetic subWords divWords) :=
  EncodedCacheScalarResult.code_bound layout.good P comparison correct _ _ _ port scalar scalarWordsBound
    (BLSExtractArithmetic.good_bounded layout.arithmetic sub subBound subBuffers _ divide divBound)
include scalarWordsBound subBound negBound divBound in
theorem bad_words : ((badCode layout P comparison correct sub negate divide subBuffers reserve negBuffers divBuffers port scalar).lower port).descriptionWords ≤
    EncodedCacheScalarResult.codeBudget (base := base) (key := key) (val := .pair val val) layout.bad
      (PairSampling.codeBudget layout.cache.value layout.cache.value scalarWords scalarWords)
      (BLSExtractArithmetic.badCode layout.arithmetic subWords negWords divWords) :=
  EncodedCacheScalarResult.code_bound (base := base) (key := key) (val := .pair val val) layout.bad P comparison correct _ _ _ port _
    (PairSampling.code_bound layout.cache.value layout.cache.value layout.cache.wordFits layout.cache.pairValueFits port scalar scalar scalarWordsBound scalarWordsBound)
    (BLSExtractArithmetic.bad_bounded layout.arithmetic sub subBound subBuffers _ negate negBound negBuffers divide divBound)
end Signatures.Runtime.CaliperBackend.BLSFinalTarget
