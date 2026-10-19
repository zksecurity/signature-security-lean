import Signatures.Runtime.Caliper.BLSTokensLayout

/-! Complete BLS transcript evaluators from stored tokens, coefficients and
cache. Row preparation, encoded zeros, scalar/pair arithmetic and private
sampling all execute here; no complete evaluator implementation is assumed. -/
namespace Signatures.Runtime.CaliperBackend.BLSTokens
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat} {Atom : Type} {base : Atom → Type} {key val : Ty Atom} {G : Type}
    [DecidableEq (key.Value base)] [Zero (val.Value base)] [Mul (val.Value base)] [Add (val.Value base)]
    (layout : Layouts w (key.Value base) G (val.Value base))
    (zeroValid : layout.rows.accumulation.cache.value.valid 0)
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    (mul : Implementation .unit layout.rows.accumulation.arithmetic.pair layout.rows.accumulation.cache.value (fun value => value.1 * value.2))
    (add : Implementation .unit layout.rows.accumulation.arithmetic.pair layout.rows.accumulation.cache.value (fun value => value.1 + value.2))
    {slots : Nat} (mulBuffers : mul.program.code.memBound ≤ slots) (reserve : slots + 4 < 2 ^ w)
    (addBuffers : add.program.code.memBound ≤ slots)
    {I : Type} {spec : OracleSpec I}

def goodCode (port : Interactive.Port w spec) (scalar : Interactive.Code w) : Interactive.Code w :=
  TokenEvaluation.code layout.good (zero layout zeroValid) (zero layout zeroValid) (zero layout zeroValid) P comparison correct
    (BLSPrivateAccumulate.goodUpdate layout.rows.accumulation mul add mulBuffers reserve)
    (BLSPrivateAccumulate.goodUpdate_buffers layout.rows.accumulation mul add mulBuffers reserve addBuffers)
    (BLSPrivateAccumulate.good_reserve layout.rows.accumulation reserve) port scalar
def badCode (port : Interactive.Port w spec) (scalar : Interactive.Code w) : Interactive.Code w :=
  TokenEvaluation.code (base := base) (key := key) (val := .pair val val) layout.bad
    (zero layout zeroValid) (pairZero layout zeroValid) (pairZero layout zeroValid) P comparison correct
    (BLSPrivateAccumulate.badUpdate layout.rows.accumulation mul add mulBuffers reserve addBuffers)
    (BLSPrivateAccumulate.badUpdate_buffers layout.rows.accumulation mul add mulBuffers reserve addBuffers)
    (BLSPrivateAccumulate.bad_reserve layout.rows.accumulation reserve) port
    (BLSPrivateAccumulate.pairSampler layout.rows.accumulation port scalar)
def goodDenote (source : OracleComp spec layout.rows.accumulation.cache.value.Value) :
    layout.good.input.Value → OracleComp spec layout.rows.good.state.Value :=
  TokenEvaluation.denote layout.good (zero layout zeroValid) (zero layout zeroValid) (zero layout zeroValid) P comparison correct
    (BLSPrivateAccumulate.goodUpdate layout.rows.accumulation mul add mulBuffers reserve)
    (BLSPrivateAccumulate.goodUpdate_buffers layout.rows.accumulation mul add mulBuffers reserve addBuffers)
    (BLSPrivateAccumulate.good_reserve layout.rows.accumulation reserve) source
def badDenote (source : OracleComp spec layout.rows.accumulation.cache.value.Value) :
    layout.bad.input.Value → OracleComp spec layout.rows.bad.state.Value :=
  TokenEvaluation.denote (base := base) (key := key) (val := .pair val val) layout.bad
    (zero layout zeroValid) (pairZero layout zeroValid) (pairZero layout zeroValid) P comparison correct
    (BLSPrivateAccumulate.badUpdate layout.rows.accumulation mul add mulBuffers reserve addBuffers)
    (BLSPrivateAccumulate.badUpdate_buffers layout.rows.accumulation mul add mulBuffers reserve addBuffers)
    (BLSPrivateAccumulate.bad_reserve layout.rows.accumulation reserve)
    (BLSPrivateAccumulate.pairSource layout.rows.accumulation source)

variable (port : Interactive.Port w spec) {source : OracleComp spec layout.rows.accumulation.cache.value.Value} {scalar : Interactive.Code w}
    (scalarCorrect : Interactive.Refines port .unit layout.rows.accumulation.cache.lookup.unit.representation
      layout.rows.accumulation.cache.value.representation (fun _ => source) scalar)
include scalarCorrect in
theorem good_refines : Interactive.RefinesOn layout.good.ready port .unit layout.good.input.representation layout.rows.good.state.representation
    (goodDenote layout zeroValid P comparison correct mul add mulBuffers reserve addBuffers source)
    (goodCode layout zeroValid P comparison correct mul add mulBuffers reserve addBuffers port scalar) :=
  TokenEvaluation.refines layout.good _ _ _ P comparison correct _ _ _ port scalarCorrect
include scalarCorrect in
theorem bad_refines : Interactive.RefinesOn layout.bad.ready port .unit layout.bad.input.representation layout.rows.bad.state.representation
    (badDenote layout zeroValid P comparison correct mul add mulBuffers reserve addBuffers source)
    (badCode layout zeroValid P comparison correct mul add mulBuffers reserve addBuffers port scalar) :=
  TokenEvaluation.refines (base := base) (key := key) (val := .pair val val) layout.bad _ _ _ P comparison correct _ _ _ port
    (PairSampling.refines (hw := layout.rows.accumulation.cache.wordFits) (fits := layout.rows.accumulation.cache.pairValueFits) scalarCorrect scalarCorrect)

variable {scalarTime scalarWords mulTime mulWords addTime addWords : Nat}
    (scalarTimeBound : Interactive.TimeBound port .unit layout.rows.accumulation.cache.lookup.unit.representation scalar scalarTime)
    (scalarWordsBound : (scalar.lower port).descriptionWords ≤ scalarWords)
    (mulBound : mul.BoundedBy mulTime mulWords) (addBound : add.BoundedBy addTime addWords)
include scalarCorrect scalarTimeBound mulBound addBound in
theorem good_time : Interactive.TimeBoundOn layout.good.ready port .unit layout.good.input.representation
    (goodCode layout zeroValid P comparison correct mul add mulBuffers reserve addBuffers port scalar)
    (TokenEvaluation.timeBudget layout.good scalarTime (BLSAccumulate.goodTime layout.rows.accumulation.arithmetic mulTime addTime)) :=
  TokenEvaluation.time_bound layout.good _ _ _ P comparison correct _ _ _ port scalarCorrect scalarTimeBound
    (BLSAccumulate.good_bounded layout.rows.accumulation.arithmetic mul add mulBound addBound mulBuffers reserve)
include scalarCorrect scalarTimeBound mulBound addBound in
theorem bad_time : Interactive.TimeBoundOn layout.bad.ready port .unit layout.bad.input.representation
    (badCode layout zeroValid P comparison correct mul add mulBuffers reserve addBuffers port scalar)
    (TokenEvaluation.timeBudget (base := base) (key := key) (val := .pair val val) layout.bad
      (PairSampling.timeBudget layout.rows.accumulation.cache.value layout.rows.accumulation.cache.value scalarTime scalarTime)
      (BLSAccumulate.badTime layout.rows.accumulation.arithmetic mulTime addTime)) :=
  TokenEvaluation.time_bound (base := base) (key := key) (val := .pair val val) layout.bad _ _ _ P comparison correct _ _ _ port
    (PairSampling.refines (hw := layout.rows.accumulation.cache.wordFits) (fits := layout.rows.accumulation.cache.pairValueFits) scalarCorrect scalarCorrect)
    (PairSampling.time_bound (hw := layout.rows.accumulation.cache.wordFits) (fits := layout.rows.accumulation.cache.pairValueFits)
      scalarCorrect scalarCorrect scalarTimeBound scalarTimeBound)
    (BLSAccumulate.bad_bounded layout.rows.accumulation.arithmetic mul add mulBound addBound mulBuffers reserve addBuffers)
include scalarWordsBound mulBound addBound in
theorem good_words : ((goodCode layout zeroValid P comparison correct mul add mulBuffers reserve addBuffers port scalar).lower port).descriptionWords ≤
    TokenEvaluation.codeBudget layout.good scalarWords (BLSAccumulate.goodCode layout.rows.accumulation.arithmetic mulWords addWords) :=
  TokenEvaluation.code_bound layout.good _ _ _ P comparison correct _ _ _ port scalar scalarWordsBound
    (BLSAccumulate.good_bounded layout.rows.accumulation.arithmetic mul add mulBound addBound mulBuffers reserve)
include scalarWordsBound mulBound addBound in
theorem bad_words : ((badCode layout zeroValid P comparison correct mul add mulBuffers reserve addBuffers port scalar).lower port).descriptionWords ≤
    TokenEvaluation.codeBudget (base := base) (key := key) (val := .pair val val) layout.bad
      (PairSampling.codeBudget layout.rows.accumulation.cache.value layout.rows.accumulation.cache.value scalarWords scalarWords)
      (BLSAccumulate.badCode layout.rows.accumulation.arithmetic mulWords addWords) :=
  TokenEvaluation.code_bound (base := base) (key := key) (val := .pair val val) layout.bad _ _ _ P comparison correct _ _ _ port _
    (PairSampling.code_bound layout.rows.accumulation.cache.value layout.rows.accumulation.cache.value layout.rows.accumulation.cache.wordFits
      layout.rows.accumulation.cache.pairValueFits port scalar scalar scalarWordsBound scalarWordsBound)
    (BLSAccumulate.bad_bounded layout.rows.accumulation.arithmetic mul add mulBound addBound mulBuffers reserve addBuffers)
end Signatures.Runtime.CaliperBackend.BLSTokens
