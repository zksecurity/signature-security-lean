import Signatures.Runtime.Caliper.InteractiveInvariantBounds
import Signatures.Runtime.Caliper.SumContextBounds

/-! A generated caller step. The handler runs with the pending caller state
saved outside its footprint. The caller's local continuation then runs with the
private handler store saved outside its footprint. All transfers execute copies.
Only the caller's own continuation and the already constructed handler are
parameters; the routing and suspension/resumption code are built here. -/

namespace Signatures.Runtime.CaliperBackend.CallerStep
open Caliper OracleComp OracleSpec

variable {w : Nat} {C Q R B S : Type}

structure Layouts (w : Nat) (C Q R B S : Type) where
  state : Representation w C
  request : Representation w Q
  reply : Representation w R
  result : Representation w B
  store : Representation w S
  fits : 8 * (1 + state.encoding.words + request.encoding.words + reply.encoding.words +
    result.encoding.words + store.encoding.words) < 2 ^ w
  width : 16 < 2 ^ w

variable (layout : Layouts w C Q R B S)

def pending : Representation w (Q × C) := layout.request.prod layout.state (by have := layout.fits; omega)
def request : Representation w (Q × S) := layout.request.prod layout.store (by have := layout.fits; omega)
def reply : Representation w (R × S) := layout.reply.prod layout.store (by have := layout.fits; omega)
def resume : Representation w (C × R) := layout.state.prod layout.reply (by have := layout.fits; omega)
def next : Representation w (B ⊕ (Q × C)) := layout.result.sum (pending layout) (width_pos layout.width) (by
  have := layout.fits
  change 1 + max layout.result.encoding.words (layout.request.encoding.words + layout.state.encoding.words) < 2 ^ w
  omega)
def frame : Representation w ((Q × C) × S) := (pending layout).prod layout.store (by
  have := layout.fits
  change layout.request.encoding.words + layout.state.encoding.words + layout.store.encoding.words < 2 ^ w
  omega)
def output : Representation w ((B ⊕ (Q × C)) × S) := (next layout).prod layout.store (by
  have := layout.fits
  change 1 + max layout.result.encoding.words (layout.request.encoding.words + layout.state.encoding.words) +
    layout.store.encoding.words < 2 ^ w
  omega)
def savedRequest : Representation w ((Q × S) × C) := (request layout).prod layout.state (by
  have := layout.fits
  change layout.request.encoding.words + layout.store.encoding.words + layout.state.encoding.words < 2 ^ w
  omega)
def savedReply : Representation w ((R × S) × C) := (reply layout).prod layout.state (by
  have := layout.fits
  change layout.reply.encoding.words + layout.store.encoding.words + layout.state.encoding.words < 2 ^ w
  omega)
def savedResume : Representation w ((C × R) × S) := (resume layout).prod layout.store (by
  have := layout.fits
  change layout.state.encoding.words + layout.reply.encoding.words + layout.store.encoding.words < 2 ^ w
  omega)

/-- Move the private store beside the request, retaining the pending caller
state as the final block. Reassociation alone is permitted only for equal bytes. -/
def prepare : Realizer .unit (frame layout) (savedRequest layout)
    (fun value => ((value.1.1, value.2), value.1.2)) := by
  have fits := layout.fits
  let swapped := Pairing.swap .unit (by decide) (pending layout) layout.store layout.width (frame layout).fits
  let ordered := Reorder.realizer .unit (by decide) layout.store layout.request layout.state layout.width (by omega)
  exact (swapped.then ordered).viewOutput (savedRequest layout) _ (by
    intro value
    simp [Representation.prod, Encoding.prod, Encoding.checked, savedRequest, request,
      Prod.swap, List.append_assoc])

/-- Restore the caller state beside its reply and leave the new private store
as the saved suffix for the local continuation. -/
def resumeArgs : Realizer .unit (savedReply layout) (savedResume layout)
    (fun value => ((value.2, value.1.1), value.1.2)) :=
  (Pairing.swap .unit (by decide) (reply layout) layout.state layout.width (savedReply layout).fits).viewOutput
    (savedResume layout) _ (by
      intro value
      simp [Representation.prod, Encoding.prod, Encoding.checked, savedResume, resume,
        reply, Prod.swap, List.append_assoc])

variable {I : Type} {spec : OracleSpec I} (port : Interactive.Port w spec)
    (advance : C × R → B ⊕ (Q × C))
    (continuation : Realizer .unit (resume layout) (next layout) advance)
    (localNameFits : continuation.savedBuffer < 2 ^ w)

def continueCode : Realizer .unit (savedResume layout) (output layout)
    (fun value => (advance value.1, value.2)) :=
  continuation.retain (by decide) layout.store layout.width localNameFits (savedResume layout).fits (output layout).fits

def code (handler : Interactive.Code w) : Interactive.Code w :=
  .seq (.compute (prepare layout).code)
    (.seq (Interactive.retain handler (Interactive.savedBuffer port handler)
      (request layout).encoding.words (reply layout).encoding.words layout.state.encoding.words)
      (.compute ((resumeArgs layout).then (continueCode layout advance continuation localNameFits)).code))

def denote (handler : Q × S → OracleComp spec (R × S)) (value : (Q × C) × S) :
    OracleComp spec ((B ⊕ (Q × C)) × S) :=
  (fun answer => (advance (value.1.2, answer.1), answer.2)) <$> handler (value.1.1, value.2)

/-- The readiness invariant belongs to the handler request/store pair. The
pending caller state is copied and framed by the generated code. -/
theorem refines {ready : Q × S → Prop} {handlerSource : Q × S → OracleComp spec (R × S)}
    {handler : Interactive.Code w}
    (handlerRefines : Interactive.RefinesOn ready port .unit (request layout) (reply layout) handlerSource handler) :
    Interactive.RefinesOn (fun value => ready (value.1.1, value.2)) port .unit
      (frame layout) (output layout) (denote advance handlerSource)
      (code layout port advance continuation localNameFits handler) := by
  have retained := handlerRefines.retain (by decide) layout.state layout.width
    (savedRequest layout).fits (savedReply layout).fits
  have resumed := Interactive.Refines.compute port .unit
    ((resumeArgs layout).then (continueCode layout advance continuation localNameFits))
  have invoked := retained.seq (resumed.on (fun _ => True)) (by intros; trivial)
  have prepared := (Interactive.Refines.compute port .unit (prepare layout)).on
    (fun value => ready (value.1.1, value.2))
  have combined := prepared.seq invoked (by
    intro value valid answer reached
    simp only [support_pure, Set.mem_singleton_iff] at reached
    subst answer
    exact valid)
  unfold CallerStep.denote code
  simpa only [bind_pure_comp, pure_bind, Functor.map_map, Function.comp_def] using combined

end Signatures.Runtime.CaliperBackend.CallerStep
