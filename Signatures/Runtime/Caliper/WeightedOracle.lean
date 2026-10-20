import Signatures.Runtime.Caliper.WeightedOracleLayout

/-! Executed weighted random/hash/sign service. Stored tags select the actual
handlers; random forwarding retains the complete private store by paid copying.
All component programs are constructed from the generator and local operations. -/
namespace Signatures.Runtime.CaliperBackend.WeightedOracle
open Caliper BoundedSource OracleComp OracleSpec

variable {w : Nat} {Atom : Type} {base : Atom → Type} {key val : Ty Atom} {M F C G : Type}
    [DecidableEq (key.Value base)]
    (layout : Layouts w (key.Value base) M F (val.Value base) C G)
    (capacity : Nat) (countFits : capacity < 2 ^ w)
    (storageFits : 1 + capacity * (WeightedRows.term layout.evaluation).representation.encoding.words +
      layout.signing.evaluated.representation.encoding.words < 2 ^ w)
    {generate : M → List (key.Value base × F)}
    (generator : Implementation .unit layout.message
      (GeneratedWeighted.terms layout.evaluation capacity countFits storageFits) generate)
    (randomBound : Nat) (randomFits : randomBound + 1 ≤ 2 ^ w)
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    {combine : F × (val.Value base × val.Value base) → val.Value base}
    (update : Implementation .unit layout.evaluation.combine layout.evaluation.cache.value combine)
    {updateSlots : Nat} (updateBuffers : update.program.code.memBound ≤ updateSlots) (updateReserve : updateSlots + 2 < 2 ^ w)
    (draw : Interactive.Code w)
    {respond : Bool → val.Value base × C → G}
    (response : (signing : Bool) → Implementation .unit layout.responseInput layout.point (respond signing))
    {responseSlots : Nat} (responseBuffers : ∀ signing, (response signing).program.code.memBound ≤ responseSlots)
    (responseReserve : responseSlots < 2 ^ w)

def groupValid : GroupInput layout → Prop :=
  Sum.elim (fun _ => True) (WeightedSign.valid layout.signing (generate := generate))
def valid : Input layout randomBound → Prop := Sum.elim (fun _ => True) (groupValid layout (generate := generate))

def hashCode : Interactive.Code w :=
  WeightedHash.code layout.hashing P comparison correct (UniformQuery.port randomBound layout.evaluation.cache.wordFits randomFits)
    draw (response false) (responseBuffers false) responseReserve
def signCode : Interactive.Code w :=
  WeightedSign.code layout.signing layout.zero capacity countFits storageFits generator layout.default P comparison correct
    update updateBuffers updateReserve (UniformQuery.port randomBound layout.evaluation.cache.wordFits randomFits)
    draw (response true) (responseBuffers true) responseReserve
def groupCode : Interactive.Code w :=
  Interactive.dispatch (hashCode layout randomBound randomFits P comparison correct draw response responseBuffers responseReserve)
    (signCode layout capacity countFits storageFits generator randomBound randomFits P comparison correct
      update updateBuffers updateReserve draw response responseBuffers responseReserve)
    layout.hashing.input.representation.encoding.words layout.signing.input.representation.encoding.words
def randomCode : Interactive.Code w :=
  .seq (UniformQuery.forward randomBound layout.evaluation.cache.wordFits randomFits layout.store.representation)
    (.compute (layout.randomTag randomBound randomFits).code)
def taggedGroup : Interactive.Code w :=
  .seq (groupCode layout capacity countFits storageFits generator randomBound randomFits P comparison correct
    update updateBuffers updateReserve draw response responseBuffers responseReserve)
    (.compute (layout.groupTag randomBound randomFits).code)
def code : Interactive.Code w := Interactive.dispatch (randomCode layout randomBound randomFits)
  (taggedGroup layout capacity countFits storageFits generator randomBound randomFits P comparison correct
    update updateBuffers updateReserve draw response responseBuffers responseReserve)
  (layout.randomInput randomBound randomFits).encoding.words layout.groupInput.encoding.words

def groupDenote (source : ProbComp layout.evaluation.cache.value.Value) : GroupInput layout → ProbComp layout.groupOutput.Value :=
  Sum.elim (WeightedHash.denote layout.hashing P comparison correct (response false) source)
    (WeightedSign.denote layout.signing layout.zero capacity countFits storageFits generator layout.default P comparison correct
      update updateBuffers updateReserve (response true) source)
def denote (source : ProbComp layout.evaluation.cache.value.Value) : Input layout randomBound → ProbComp (Output layout randomBound) :=
  Sum.elim (fun value => Sum.inl <$> UniformQuery.forwardSource randomBound value)
    (fun value => Sum.inr <$> groupDenote layout capacity countFits storageFits generator P comparison correct
      update updateBuffers updateReserve response source value)

variable {source : ProbComp layout.evaluation.cache.value.Value}
    (drawCorrect : Interactive.Refines (UniformQuery.port randomBound layout.evaluation.cache.wordFits randomFits) .unit
      layout.evaluation.cache.lookup.unit.representation layout.evaluation.cache.value.representation (fun _ => source) draw)

include drawCorrect in
theorem group_refines : Interactive.RefinesOn (groupValid layout (generate := generate))
    (UniformQuery.port randomBound layout.evaluation.cache.wordFits randomFits) .unit layout.groupInput layout.groupOutput.representation
    (groupDenote layout capacity countFits storageFits generator P comparison correct update updateBuffers updateReserve response source)
    (groupCode layout capacity countFits storageFits generator randomBound randomFits P comparison correct
      update updateBuffers updateReserve draw response responseBuffers responseReserve) :=
  Interactive.RefinesOn.dispatch _ _ _
    ((WeightedHash.refines layout.hashing P comparison correct _ draw (response false) (responseBuffers false) responseReserve drawCorrect).on (fun _ => True))
    (WeightedSign.refines layout.signing layout.zero capacity countFits storageFits generator layout.default P comparison correct
      update updateBuffers updateReserve _ draw (response true) (responseBuffers true) responseReserve drawCorrect)
    (width_pos layout.evaluation.cache.wordFits) layout.groupInput.fits

omit [DecidableEq (key.Value base)] in
theorem random_refines : Interactive.Refines (UniformQuery.port randomBound layout.evaluation.cache.wordFits randomFits) .unit
    (layout.randomInput randomBound randomFits) (layout.output randomBound randomFits)
    (fun value => Sum.inl <$> UniformQuery.forwardSource randomBound value) (randomCode layout randomBound randomFits) := by
  simpa only [randomCode, Layouts.randomInput, bind_pure_comp] using
    (UniformQuery.forward_refines randomBound layout.evaluation.cache.wordFits randomFits layout.store.representation
      (layout.randomOutput randomBound randomFits).fits).seq
      (Interactive.Refines.compute _ .unit (layout.randomTag randomBound randomFits))

include drawCorrect in
theorem refines : Interactive.RefinesOn (valid layout (generate := generate) randomBound)
    (UniformQuery.port randomBound layout.evaluation.cache.wordFits randomFits) .unit
    (layout.input randomBound randomFits) (layout.output randomBound randomFits)
    (denote layout capacity countFits storageFits generator randomBound P comparison correct
      update updateBuffers updateReserve response source)
    (code layout capacity countFits storageFits generator randomBound randomFits P comparison correct
      update updateBuffers updateReserve draw response responseBuffers responseReserve) := by
  have group := (group_refines layout capacity countFits storageFits generator randomBound randomFits P comparison correct
    update updateBuffers updateReserve draw response responseBuffers responseReserve drawCorrect).seq
      ((Interactive.Refines.compute _ .unit (layout.groupTag randomBound randomFits)).on (fun _ => True))
      (fun _ _ _ _ => trivial)
  have tagged :
      Interactive.RefinesOn (groupValid layout (generate := generate))
        (UniformQuery.port randomBound layout.evaluation.cache.wordFits randomFits) .unit layout.groupInput
        (layout.output randomBound randomFits)
        (fun value => Sum.inr <$> groupDenote layout capacity countFits storageFits generator P comparison correct
          update updateBuffers updateReserve response source value)
        (taggedGroup layout capacity countFits storageFits generator randomBound randomFits P comparison correct
          update updateBuffers updateReserve draw response responseBuffers responseReserve) := by
    simpa only [taggedGroup, bind_pure_comp] using group
  exact Interactive.RefinesOn.dispatch _ _ _
    ((random_refines layout randomBound randomFits).on (fun _ => True)) tagged
    (width_pos layout.evaluation.cache.wordFits) (layout.input randomBound randomFits).fits

end Signatures.Runtime.CaliperBackend.WeightedOracle
