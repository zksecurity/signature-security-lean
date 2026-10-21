import Signatures.Runtime.Caliper.SchnorrROMFreshGuardPrepare
import Signatures.Runtime.Caliper.SchnorrROMFreshGuardStepBounds

/-! Complete executed rejection test for a repeated challenge. Only the
represented saved tape is scanned. The returned true bit tells the fork
controller to reject, exactly as the original optional public-cell comparison. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.FreshGuard
open Caliper BoundedSource SchnorrROMTape
variable {w : Nat} {F : Type} [DecidableEq F] (layout : Layouts w F)

theorem bodyNameFits : (stepConstructed layout).implementation.program.savedBuffer < 2 ^ w :=
  (stepConstructed layout).nameFits layout.wordFits (by rw [body_buffers]; have := layout.wordFits; omega)
def loop := FoldImplementation.compile layout.entry (state layout) layout.scalar (argFits layout)
  (stepConstructed layout).implementation (by decide) layout.wordFits (bodyNameFits layout) layout.capacity
    (by have := layout.countFits; omega) (frameFits layout)
def result : Constructed (state layout) layout.boolean (fun value => value.2.2) :=
  (Constructed.second layout.counter (flags layout) layout.wordFits (state layout).representation.fits).then
    (Constructed.second layout.boolean layout.boolean layout.wordFits (flags layout).representation.fits)
def implementation : Implementation .unit (input layout) layout.boolean source :=
  (((prepare layout).implementation.then (loop layout)).then (result layout).implementation).castFunction (by
    funext value
    exact fold_value value.2.2 value.1 value.2.1)

def loopTime := 24 + layout.capacity * (10000 * layout.width + 1000 +
  44 * ListFold.width layout.entry.representation.encoding.words 3 layout.scalar.representation.encoding.words layout.capacity + 7)
def loopWords := 92 + layout.capacity * (40000 * layout.width + 10000 +
  169 * ListFold.width layout.entry.representation.encoding.words 3 layout.scalar.representation.encoding.words layout.capacity + 115)
theorem loop_bounded : (loop layout).BoundedBy (loopTime layout) (loopWords layout) :=
  FoldImplementation.compile_boundedBy layout.entry (state layout) layout.scalar (argFits layout)
    (stepConstructed layout).implementation layout.wordFits (bodyNameFits layout) layout.capacity
      (by have := layout.countFits; omega) (frameFits layout) _ _
        ((stepConstructed layout).bounded.mono (body_budget layout).1 (body_budget layout).2)
theorem loop_buffers : (loop layout).program.code.memBound ≤ 8 := by
  have folded := ListFold.buffers (stepConstructed layout).implementation.program.code
    layout.entry.representation.encoding.words 3 layout.scalar.representation.encoding.words layout.capacity
  have body := (stepConstructed layout).buffers_le
  rw [body_buffers] at body
  exact folded.trans (by omega)
theorem loop_names (slots : Nat) : NamesAccounted (loop layout).program.code slots :=
  FoldImplementation.compile_names _ _ _ _ _ _ _ _ _ _ ((stepConstructed layout).names slots)

def timeBudget := (prepare layout).budget.time + loopTime layout + (result layout).budget.time
def codeBudget := (prepare layout).budget.words + loopWords layout + (result layout).budget.words + 2
theorem bounded : (implementation layout).BoundedBy (timeBudget layout) (codeBudget layout) :=
  (((prepare layout).bounded.then (loop_bounded layout)).then (result layout).bounded).castFunction
    (funext fun value => fold_value value.2.2 value.1 value.2.1)
theorem buffers : (implementation layout).program.code.memBound ≤ 8 :=
  max_le (max_le ((prepare layout).buffers_le.trans (by change 2 ≤ 8; decide)) (loop_buffers layout))
    ((result layout).buffers_le.trans (by change 2 ≤ 8; decide))
theorem names (slots : Nat) : NamesAccounted (implementation layout).program.code slots :=
  (((prepare layout).names slots).seq (loop_names layout slots)).seq ((result layout).names slots)
def constructed : Constructed (input layout) layout.boolean source where
  implementation := implementation layout
  budget := ⟨timeBudget layout, codeBudget layout⟩
  bounded := bounded layout
  buffers := 8
  buffers_le := buffers layout
  names := names layout

end Signatures.Runtime.CaliperBackend.SchnorrROM.FreshGuard
