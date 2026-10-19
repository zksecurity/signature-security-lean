import Signatures.Runtime.Caliper.BLSPrivateAccumulateLayout

/-! BLS private cache reads with actual scalar arithmetic. There is no supplied
whole-update or cache-controller implementation: both are composed here from
scalar multiplication, addition and a scalar sampler. -/
namespace Signatures.Runtime.CaliperBackend.BLSPrivateAccumulate
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat} {Atom : Type} {base : Atom → Type} {key val : Ty Atom}
    [DecidableEq (key.Value base)] [Mul (val.Value base)] [Add (val.Value base)]
    (layout : Layouts w (key.Value base) (val.Value base))
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    (mul : Implementation .unit layout.arithmetic.pair layout.cache.value (fun value => value.1 * value.2))
    (add : Implementation .unit layout.arithmetic.pair layout.cache.value (fun value => value.1 + value.2))
    {slots : Nat} (mulBuffers : mul.program.code.memBound ≤ slots) (reserve : slots + 4 < 2 ^ w)
    (addBuffers : add.program.code.memBound ≤ slots)
    {I : Type} {spec : OracleSpec I}

def pairSampler (port : Interactive.Port w spec) (scalar : Interactive.Code w) : Interactive.Code w :=
  PairSampling.code layout.cache.value layout.cache.value layout.cache.wordFits layout.cache.pairValueFits port scalar scalar
def pairSource (source : OracleComp spec layout.cache.value.Value) : OracleComp spec layout.bad.cache.value.Value :=
  PairSampling.denote layout.cache.value layout.cache.value layout.cache.pairValueFits source source

def goodCode (port : Interactive.Port w spec) (scalar : Interactive.Code w) : Interactive.Code w :=
  EncodedCacheAccumulate.code layout.good P comparison correct (goodUpdate layout mul add mulBuffers reserve)
    (goodUpdate_buffers layout mul add mulBuffers reserve addBuffers) (good_reserve layout reserve) port scalar
def badCode (port : Interactive.Port w spec) (scalar : Interactive.Code w) : Interactive.Code w :=
  EncodedCacheAccumulate.code (base := base) (key := key) (val := .pair val val) layout.bad P comparison correct
    (badUpdate layout mul add mulBuffers reserve addBuffers)
    (badUpdate_buffers layout mul add mulBuffers reserve addBuffers) (bad_reserve layout reserve) port (pairSampler layout port scalar)
def goodDenote (source : OracleComp spec layout.cache.value.Value) : layout.good.input.Value → OracleComp spec (CacheRead.output layout.good.cache).Value :=
  EncodedCacheAccumulate.denote layout.good P comparison correct (goodUpdate layout mul add mulBuffers reserve)
    (goodUpdate_buffers layout mul add mulBuffers reserve addBuffers) (good_reserve layout reserve) source
def badDenote (source : OracleComp spec layout.cache.value.Value) : layout.bad.input.Value → OracleComp spec (CacheRead.output layout.bad.cache).Value :=
  EncodedCacheAccumulate.denote (base := base) (key := key) (val := .pair val val) layout.bad P comparison correct
    (badUpdate layout mul add mulBuffers reserve addBuffers)
    (badUpdate_buffers layout mul add mulBuffers reserve addBuffers) (bad_reserve layout reserve) (pairSource layout source)

variable (port : Interactive.Port w spec) {source : OracleComp spec layout.cache.value.Value} {scalar : Interactive.Code w}
    (scalarCorrect : Interactive.Refines port .unit layout.cache.lookup.unit.representation layout.cache.value.representation
      (fun _ => source) scalar)
include scalarCorrect in
theorem good_refines : Interactive.Refines port .unit layout.good.input.representation (CacheRead.output layout.good.cache).representation
    (goodDenote layout P comparison correct mul add mulBuffers reserve addBuffers source)
    (goodCode layout P comparison correct mul add mulBuffers reserve addBuffers port scalar) :=
  EncodedCacheAccumulate.refines layout.good P comparison correct _ _ _ port source scalar scalarCorrect
include scalarCorrect in
theorem bad_refines : Interactive.Refines port .unit layout.bad.input.representation (CacheRead.output layout.bad.cache).representation
    (badDenote layout P comparison correct mul add mulBuffers reserve addBuffers source)
    (badCode layout P comparison correct mul add mulBuffers reserve addBuffers port scalar) :=
  EncodedCacheAccumulate.refines (base := base) (key := key) (val := .pair val val) layout.bad P comparison correct _ _ _ port
    (pairSource layout source) (pairSampler layout port scalar)
    (PairSampling.refines (hw := layout.cache.wordFits) (fits := layout.cache.pairValueFits) scalarCorrect scalarCorrect)

variable {scalarTime scalarWords mulTime mulWords addTime addWords : Nat}
    (scalarTimeBound : Interactive.TimeBound port .unit layout.cache.lookup.unit.representation scalar scalarTime)
    (scalarWordsBound : (scalar.lower port).descriptionWords ≤ scalarWords)
    (mulBound : mul.BoundedBy mulTime mulWords) (addBound : add.BoundedBy addTime addWords)
include scalarCorrect scalarTimeBound mulBound addBound in
theorem good_time : Interactive.TimeBound port .unit layout.good.input.representation
    (goodCode layout P comparison correct mul add mulBuffers reserve addBuffers port scalar)
    (EncodedCacheAccumulate.timeBudget layout.good scalarTime (BLSAccumulate.goodTime layout.arithmetic mulTime addTime)) :=
  EncodedCacheAccumulate.time_bound layout.good P comparison correct _ _ _ port scalarCorrect scalarTimeBound
    (BLSAccumulate.good_bounded layout.arithmetic mul add mulBound addBound mulBuffers reserve)
include scalarCorrect scalarTimeBound mulBound addBound in
theorem bad_time : Interactive.TimeBound port .unit layout.bad.input.representation
    (badCode layout P comparison correct mul add mulBuffers reserve addBuffers port scalar)
    (EncodedCacheAccumulate.timeBudget (base := base) (key := key) (val := .pair val val) layout.bad
      (PairSampling.timeBudget layout.cache.value layout.cache.value scalarTime scalarTime)
      (BLSAccumulate.badTime layout.arithmetic mulTime addTime)) :=
  EncodedCacheAccumulate.time_bound (base := base) (key := key) (val := .pair val val) layout.bad P comparison correct _ _ _ port
    (PairSampling.refines (hw := layout.cache.wordFits) (fits := layout.cache.pairValueFits) scalarCorrect scalarCorrect)
    (PairSampling.time_bound (hw := layout.cache.wordFits) (fits := layout.cache.pairValueFits) scalarCorrect scalarCorrect scalarTimeBound scalarTimeBound)
    (BLSAccumulate.bad_bounded layout.arithmetic mul add mulBound addBound mulBuffers reserve addBuffers)
include scalarWordsBound mulBound addBound in
theorem good_words : ((goodCode layout P comparison correct mul add mulBuffers reserve addBuffers port scalar).lower port).descriptionWords ≤
    EncodedCacheAccumulate.codeBudget layout.good scalarWords (BLSAccumulate.goodCode layout.arithmetic mulWords addWords) :=
  EncodedCacheAccumulate.code_bound layout.good P comparison correct _ _ _ port scalar scalarWordsBound
    (BLSAccumulate.good_bounded layout.arithmetic mul add mulBound addBound mulBuffers reserve)
include scalarWordsBound mulBound addBound in
theorem bad_words : ((badCode layout P comparison correct mul add mulBuffers reserve addBuffers port scalar).lower port).descriptionWords ≤
    EncodedCacheAccumulate.codeBudget (base := base) (key := key) (val := .pair val val) layout.bad
      (PairSampling.codeBudget layout.cache.value layout.cache.value scalarWords scalarWords)
      (BLSAccumulate.badCode layout.arithmetic mulWords addWords) :=
  EncodedCacheAccumulate.code_bound (base := base) (key := key) (val := .pair val val) layout.bad P comparison correct _ _ _ port _
    (PairSampling.code_bound layout.cache.value layout.cache.value layout.cache.wordFits layout.cache.pairValueFits port scalar scalar scalarWordsBound scalarWordsBound)
    (BLSAccumulate.bad_bounded layout.arithmetic mul add mulBound addBound mulBuffers reserve addBuffers)

end Signatures.Runtime.CaliperBackend.BLSPrivateAccumulate
