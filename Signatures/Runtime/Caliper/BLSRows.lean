import Signatures.Runtime.Caliper.BLSRowsLayout

/-! BLS row evaluation with constructed scalar/pair arithmetic and sampling.
Only named scalar routines and their local contracts are parameters. -/
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
    {I : Type} {spec : OracleSpec I}

def pairDefault : layout.bad.accumulation.cache.value.Value := ⟨(default.val, default.val), default.property, default.property⟩

def goodCode (capacity : Nat) (port : Interactive.Port w spec) (scalar : Interactive.Code w) : Interactive.Code w :=
  RowFold.code (base := base) (key := key) (val := val) layout.good default P comparison correct
    (BLSPrivateAccumulate.goodUpdate layout.accumulation mul add mulBuffers reserve)
    (BLSPrivateAccumulate.goodUpdate_buffers layout.accumulation mul add mulBuffers reserve addBuffers)
    (BLSPrivateAccumulate.good_reserve layout.accumulation reserve) capacity port scalar
def goodDenote (source : OracleComp spec layout.accumulation.cache.value.Value) {capacity : Nat}
    (value : RowFold.Input layout.good capacity) : OracleComp spec layout.good.state.Value :=
  RowFold.denote (base := base) (key := key) (val := val) layout.good default P comparison correct
    (BLSPrivateAccumulate.goodUpdate layout.accumulation mul add mulBuffers reserve)
    (BLSPrivateAccumulate.goodUpdate_buffers layout.accumulation mul add mulBuffers reserve addBuffers)
    (BLSPrivateAccumulate.good_reserve layout.accumulation reserve) source value

def badCode (capacity : Nat) (port : Interactive.Port w spec) (scalar : Interactive.Code w) : Interactive.Code w :=
  RowFold.code (base := base) (key := key) (val := .pair val val) layout.bad (pairDefault layout default) P comparison correct
    (BLSPrivateAccumulate.badUpdate layout.accumulation mul add mulBuffers reserve addBuffers)
    (BLSPrivateAccumulate.badUpdate_buffers layout.accumulation mul add mulBuffers reserve addBuffers)
    (BLSPrivateAccumulate.bad_reserve layout.accumulation reserve) capacity port
    (BLSPrivateAccumulate.pairSampler layout.accumulation port scalar)
def badDenote (source : OracleComp spec layout.accumulation.cache.value.Value) {capacity : Nat}
    (value : RowFold.Input (base := base) (key := key) (val := .pair val val) layout.bad capacity) : OracleComp spec layout.bad.state.Value :=
  RowFold.denote (base := base) (key := key) (val := .pair val val) layout.bad (pairDefault layout default) P comparison correct
    (BLSPrivateAccumulate.badUpdate layout.accumulation mul add mulBuffers reserve addBuffers)
    (BLSPrivateAccumulate.badUpdate_buffers layout.accumulation mul add mulBuffers reserve addBuffers)
    (BLSPrivateAccumulate.bad_reserve layout.accumulation reserve)
    (BLSPrivateAccumulate.pairSource layout.accumulation source) value

variable (port : Interactive.Port w spec) {source : OracleComp spec layout.accumulation.cache.value.Value} {scalar : Interactive.Code w}
    (scalarCorrect : Interactive.Refines port .unit layout.accumulation.cache.lookup.unit.representation
      layout.accumulation.cache.value.representation (fun _ => source) scalar)
    (capacity : Nat) (countFits : capacity < 2 ^ w)

include scalarCorrect in
theorem good_refines
    (storageFits : 1 + capacity * layout.good.row.representation.encoding.words + layout.good.state.representation.encoding.words < 2 ^ w) :
    Interactive.RefinesOn (RowFold.valid layout.good) port .unit (RowFold.input layout.good capacity countFits storageFits)
      layout.good.state.representation
      (goodDenote layout default P comparison correct mul add mulBuffers reserve addBuffers source)
      (goodCode layout default P comparison correct mul add mulBuffers reserve addBuffers capacity port scalar) :=
  RowFold.refines (base := base) (key := key) (val := val) layout.good default P comparison correct
    (BLSPrivateAccumulate.goodUpdate layout.accumulation mul add mulBuffers reserve)
    (BLSPrivateAccumulate.goodUpdate_buffers layout.accumulation mul add mulBuffers reserve addBuffers)
    (BLSPrivateAccumulate.good_reserve layout.accumulation reserve) port scalarCorrect capacity countFits storageFits

include scalarCorrect in
theorem bad_refines
    (storageFits : 1 + capacity * layout.bad.row.representation.encoding.words + layout.bad.state.representation.encoding.words < 2 ^ w) :
    Interactive.RefinesOn (RowFold.valid (base := base) (key := key) (val := .pair val val) layout.bad) port .unit (RowFold.input (base := base) (key := key) (val := .pair val val) layout.bad capacity countFits storageFits)
      layout.bad.state.representation
      (badDenote layout default P comparison correct mul add mulBuffers reserve addBuffers source)
      (badCode layout default P comparison correct mul add mulBuffers reserve addBuffers capacity port scalar) :=
  RowFold.refines (base := base) (key := key) (val := .pair val val) layout.bad (pairDefault layout default) P comparison correct
    (BLSPrivateAccumulate.badUpdate layout.accumulation mul add mulBuffers reserve addBuffers)
    (BLSPrivateAccumulate.badUpdate_buffers layout.accumulation mul add mulBuffers reserve addBuffers)
    (BLSPrivateAccumulate.bad_reserve layout.accumulation reserve) port
    (PairSampling.refines (hw := layout.accumulation.cache.wordFits) (fits := layout.accumulation.cache.pairValueFits) scalarCorrect scalarCorrect) capacity countFits storageFits

variable {scalarTime scalarWords mulTime mulWords addTime addWords : Nat}
    (scalarTimeBound : Interactive.TimeBound port .unit layout.accumulation.cache.lookup.unit.representation scalar scalarTime)
    (scalarWordsBound : (scalar.lower port).descriptionWords ≤ scalarWords)
    (mulBound : mul.BoundedBy mulTime mulWords) (addBound : add.BoundedBy addTime addWords)

include scalarCorrect scalarTimeBound mulBound addBound in
theorem good_time
    (storageFits : 1 + capacity * layout.good.row.representation.encoding.words + layout.good.state.representation.encoding.words < 2 ^ w) :
    Interactive.TimeBoundOn (RowFold.valid layout.good) port .unit (RowFold.input layout.good capacity countFits storageFits)
      (goodCode layout default P comparison correct mul add mulBuffers reserve addBuffers capacity port scalar)
      (RowFold.timeBudget layout.good capacity scalarTime (BLSAccumulate.goodTime layout.accumulation.arithmetic mulTime addTime)) :=
  RowFold.time_bound (base := base) (key := key) (val := val) layout.good default P comparison correct
    (BLSPrivateAccumulate.goodUpdate layout.accumulation mul add mulBuffers reserve)
    (BLSPrivateAccumulate.goodUpdate_buffers layout.accumulation mul add mulBuffers reserve addBuffers)
    (BLSPrivateAccumulate.good_reserve layout.accumulation reserve) port scalarCorrect capacity countFits storageFits scalarTimeBound (BLSAccumulate.good_bounded layout.accumulation.arithmetic mul add mulBound addBound mulBuffers reserve)

include scalarWordsBound mulBound addBound in
theorem good_words :
    ((goodCode layout default P comparison correct mul add mulBuffers reserve addBuffers capacity port scalar).lower port).descriptionWords ≤
      RowFold.codeBudget layout.good capacity scalarWords (BLSAccumulate.goodCode layout.accumulation.arithmetic mulWords addWords) :=
  RowFold.code_bound (base := base) (key := key) (val := val) layout.good default P comparison correct
    (BLSPrivateAccumulate.goodUpdate layout.accumulation mul add mulBuffers reserve)
    (BLSPrivateAccumulate.goodUpdate_buffers layout.accumulation mul add mulBuffers reserve addBuffers)
    (BLSPrivateAccumulate.good_reserve layout.accumulation reserve) port capacity _ scalarWordsBound (BLSAccumulate.good_bounded layout.accumulation.arithmetic mul add mulBound addBound mulBuffers reserve)

include scalarCorrect scalarTimeBound mulBound addBound in
theorem bad_time
    (storageFits : 1 + capacity * layout.bad.row.representation.encoding.words + layout.bad.state.representation.encoding.words < 2 ^ w) :
    Interactive.TimeBoundOn (RowFold.valid (base := base) (key := key) (val := .pair val val) layout.bad) port .unit (RowFold.input (base := base) (key := key) (val := .pair val val) layout.bad capacity countFits storageFits)
      (badCode layout default P comparison correct mul add mulBuffers reserve addBuffers capacity port scalar)
      (RowFold.timeBudget (base := base) (key := key) (val := .pair val val) layout.bad capacity
    (PairSampling.timeBudget layout.accumulation.cache.value layout.accumulation.cache.value scalarTime scalarTime) (BLSAccumulate.badTime layout.accumulation.arithmetic mulTime addTime)) :=
  RowFold.time_bound (base := base) (key := key) (val := .pair val val) layout.bad (pairDefault layout default) P comparison correct
    (BLSPrivateAccumulate.badUpdate layout.accumulation mul add mulBuffers reserve addBuffers)
    (BLSPrivateAccumulate.badUpdate_buffers layout.accumulation mul add mulBuffers reserve addBuffers)
    (BLSPrivateAccumulate.bad_reserve layout.accumulation reserve) port
    (PairSampling.refines (hw := layout.accumulation.cache.wordFits) (fits := layout.accumulation.cache.pairValueFits) scalarCorrect scalarCorrect) capacity countFits storageFits
    (PairSampling.time_bound (hw := layout.accumulation.cache.wordFits) (fits := layout.accumulation.cache.pairValueFits) scalarCorrect scalarCorrect scalarTimeBound scalarTimeBound) (BLSAccumulate.bad_bounded layout.accumulation.arithmetic mul add mulBound addBound mulBuffers reserve addBuffers)

include scalarWordsBound mulBound addBound in
theorem bad_words :
    ((badCode layout default P comparison correct mul add mulBuffers reserve addBuffers capacity port scalar).lower port).descriptionWords ≤
      RowFold.codeBudget (base := base) (key := key) (val := .pair val val) layout.bad capacity
    (PairSampling.codeBudget layout.accumulation.cache.value layout.accumulation.cache.value scalarWords scalarWords) (BLSAccumulate.badCode layout.accumulation.arithmetic mulWords addWords) :=
  RowFold.code_bound (base := base) (key := key) (val := .pair val val) layout.bad (pairDefault layout default) P comparison correct
    (BLSPrivateAccumulate.badUpdate layout.accumulation mul add mulBuffers reserve addBuffers)
    (BLSPrivateAccumulate.badUpdate_buffers layout.accumulation mul add mulBuffers reserve addBuffers)
    (BLSPrivateAccumulate.bad_reserve layout.accumulation reserve) port capacity _
    (PairSampling.code_bound layout.accumulation.cache.value layout.accumulation.cache.value layout.accumulation.cache.wordFits layout.accumulation.cache.pairValueFits port scalar scalar scalarWordsBound scalarWordsBound) (BLSAccumulate.bad_bounded layout.accumulation.arithmetic mul add mulBound addBound mulBuffers reserve addBuffers)

end Signatures.Runtime.CaliperBackend.BLSRows
