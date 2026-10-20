import Signatures.Runtime.Caliper.CallerControl
import Signatures.Runtime.Caliper.StatefulCacheBuffers

/-! Buffer-name extents for generated caller control. Loop iterations reuse the
same scratch names, so these bounds depend on local code, not the fuel or the
stored program length. A retained value occupies one additional buffer. -/

namespace Signatures.Runtime.CaliperBackend
open Caliper

variable {w : Nat}

theorem Realizer.retain_buffers {A B S : Type} {cost : CostModel}
    {input : Representation w A} {output : Representation w B} {f : A → B}
    (body : Realizer cost input output f) (allocation : 1 ≤ cost.allocPerWord)
    (saved : Representation w S) (hw : 16 < 2 ^ w)
    (nameFits : body.savedBuffer < 2 ^ w)
    (inputFits : input.encoding.words + saved.encoding.words < 2 ^ w)
    (outputFits : output.encoding.words + saved.encoding.words < 2 ^ w) :
    (body.retain allocation saved hw nameFits inputFits outputFits).code.memBound ≤
      max 2 body.code.memBound + 1 :=
  (Retain.code_names body.code (max 2 body.code.memBound) input.encoding.words
    output.encoding.words saved.encoding.words (Nat.le_max_left _ _) (Nat.le_max_right _ _)).2

namespace Interactive
variable {I : Type} {spec : OracleSpec I} (port : Port w spec)

theorem loop_buffers (body stop : Code w) (resultWords stateWords fuel : Nat) :
    ((loop body stop resultWords stateWords fuel).lower port).memBound ≤
      max 2 (max (body.lower port).memBound (stop.lower port).memBound) := by
  induction fuel with
  | zero => simp only [loop]; omega
  | succ fuel ih =>
    have dispatched := dispatch_buffers port (.compute .skip)
      (loop body stop resultWords stateWords fuel) resultWords stateWords
    simp only [Code.lower, WordIO.Code.memBound, Stmt.memBound] at dispatched
    simp only [loop, Code.lower, WordIO.Code.memBound]
    omega

end Interactive

namespace CallerStep
variable {C Q R B S : Type} (layout : Layouts w C Q R B S)

theorem prepare_buffers : (prepare layout).code.memBound ≤ 2 := by
  have swapped := Reorder.buffers (w := w) (pending layout).encoding.words layout.store.encoding.words 0
  have ordered := Reorder.buffers (w := w) layout.store.encoding.words layout.request.encoding.words layout.state.encoding.words
  change max _ _ ≤ _
  exact max_le swapped ordered

theorem resumeArgs_buffers : (resumeArgs layout).code.memBound ≤ 2 :=
  Reorder.buffers (w := w) (reply layout).encoding.words layout.state.encoding.words 0

variable {I : Type} {spec : OracleSpec I} (port : Interactive.Port w spec)
    (advance : C × R → B ⊕ (Q × C))
    (continuation : Realizer .unit (resume layout) (next layout) advance)
    (localNameFits : continuation.savedBuffer < 2 ^ w) (handler : Interactive.Code w)

theorem buffers : ((code layout port advance continuation localNameFits handler).lower port).memBound ≤
    max 2 (max (handler.lower port).memBound continuation.code.memBound) + 1 := by
  have prepared := prepare_buffers layout
  have resumed := resumeArgs_buffers layout
  have retained := Interactive.retain_buffers port handler
    (request layout).encoding.words (reply layout).encoding.words layout.state.encoding.words
  have continued := continuation.retain_buffers (by decide) layout.store layout.width localNameFits
    (savedResume layout).fits (output layout).fits
  change (continueCode layout advance continuation localNameFits).code.memBound ≤ _ at continued
  change max (prepare layout).code.memBound (max _
    (max (resumeArgs layout).code.memBound (continueCode layout advance continuation localNameFits).code.memBound)) ≤ _
  omega

end CallerStep

namespace CallerControl
variable {C Q R B S : Type} (layout : CallerStep.Layouts w C Q R B S)

theorem distribute_buffers : (distribute layout).code.memBound ≤ 3 :=
  SumContext.buffers _ _ _ _ _

theorem done_buffers : (done layout).code.memBound ≤ 4 := by
  have tagged := inl_names layout.result (CallerStep.pending layout) layout.width (CallerStep.next layout).fits
  have tagBuffers := tagged.buffers
  have retained := (inlRealizer .unit (by decide) layout.result (CallerStep.pending layout)
    layout.width (CallerStep.next layout).fits).retain_buffers (by decide) layout.store layout.width
    (by have := layout.width; dsimp only [Realizer.savedBuffer]; omega)
    (result layout).fits (CallerStep.output layout).fits
  exact retained.trans (by have := tagged.buffers; omega)

theorem stop_buffers : (stop layout).code.memBound ≤ 4 := by
  have tagged := inr_names layout.result (CallerStep.pending layout) layout.width (CallerStep.next layout).fits
  have tagBuffers := tagged.buffers
  have retained := (inrRealizer .unit (by decide) layout.result (CallerStep.pending layout)
    layout.width (CallerStep.next layout).fits).retain_buffers (by decide) layout.store layout.width
    (by have := layout.width; dsimp only [Realizer.savedBuffer]; omega)
    (CallerStep.frame layout).fits (CallerStep.output layout).fits
  exact retained.trans (by have := tagged.buffers; omega)

theorem route_buffers : (route layout).code.memBound ≤ 4 := by
  have distributed := distribute_buffers layout
  have finished := done_buffers layout
  have taggedLeft := (inl_names (CallerStep.output layout) (CallerStep.frame layout) layout.width (iteration layout).fits).buffers
  have taggedRight := (inr_names (CallerStep.output layout) (CallerStep.frame layout) layout.width (iteration layout).fits).buffers
  change max (distribute layout).code.memBound (Dispatch.code _ _ _ _).memBound ≤ 4
  refine max_le (distributed.trans (by decide)) ((Dispatch.buffers _ _ _ _).trans ?_)
  change max 2 (max (max _ _) _) ≤ 4
  omega

variable {I : Type} {spec : OracleSpec I} (port : Interactive.Port w spec)
    (advance : C × R → B ⊕ (Q × C))
    (continuation : Realizer .unit (CallerStep.resume layout) (CallerStep.next layout) advance)
    (localNameFits : continuation.savedBuffer < 2 ^ w) (handler : Interactive.Code w)

theorem fromState_buffers (fuel : Nat) :
    ((fromState layout port advance continuation localNameFits handler fuel).lower port).memBound ≤
      max 4 (max (handler.lower port).memBound continuation.code.memBound) + 1 := by
  have stepped := CallerStep.buffers layout port advance continuation localNameFits handler
  have routed := route_buffers layout
  have stopped := stop_buffers layout
  have looped := Interactive.loop_buffers port (body layout port advance continuation localNameFits handler)
    (.compute (stop layout).code) (CallerStep.output layout).encoding.words (CallerStep.frame layout).encoding.words fuel
  change ((fromState layout port advance continuation localNameFits handler fuel).lower port).memBound ≤ _ at looped
  simp only [body, Interactive.Code.lower, WordIO.Code.memBound] at looped
  omega

theorem fromPacket_buffers (fuel : Nat) :
    ((fromPacket layout port advance continuation localNameFits handler fuel).lower port).memBound ≤
      max 4 (max (handler.lower port).memBound continuation.code.memBound) + 1 := by
  have distributed := distribute_buffers layout
  have finished := done_buffers layout
  have stepped := fromState_buffers layout port advance continuation localNameFits handler fuel
  have dispatched := Interactive.dispatch_buffers port (.compute (done layout).code)
    (fromState layout port advance continuation localNameFits handler fuel)
    (result layout).encoding.words (CallerStep.frame layout).encoding.words
  simp only [Interactive.Code.lower, WordIO.Code.memBound] at dispatched
  change max (distribute layout).code.memBound _ ≤ _
  omega

theorem program_buffers {A : Type} (input : Representation w A) (initial : A → B ⊕ (Q × C))
    (initialCode : Realizer .unit input (CallerStep.next layout) initial)
    (initialNameFits : initialCode.savedBuffer < 2 ^ w)
    (inputFits : input.encoding.words + layout.store.encoding.words < 2 ^ w) (fuel : Nat) :
    ((program layout port advance continuation localNameFits handler input initial initialCode initialNameFits inputFits fuel).lower port).memBound ≤
      max 4 (max (handler.lower port).memBound (max continuation.code.memBound initialCode.code.memBound)) + 1 := by
  have started := initialCode.retain_buffers (by decide) layout.store layout.width initialNameFits inputFits (CallerStep.output layout).fits
  have rest := fromPacket_buffers layout port advance continuation localNameFits handler fuel
  change max (initialCode.retain (by decide) layout.store layout.width initialNameFits inputFits (CallerStep.output layout).fits).code.memBound _ ≤ _
  omega

end CallerControl
end Signatures.Runtime.CaliperBackend
