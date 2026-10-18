import Signatures.Runtime.Caliper.ExpressionEmission

/-! Successful compilation of a complete original fixed-layout fold, including
its argument frame. Scratch-buffer requirements are independent of capacity. -/

namespace Signatures.Runtime.CaliperBackend.SourceExpression

open Caliper BoundedSource

variable {w : Nat} {Atom : Type} {base : Atom → Type} {Op : Ty Atom → Ty Atom → Type}
    {P : Primitives base Op} {hw : 16 < 2 ^ w}

theorem Compilation.Emits.fold {Γ : List (Ty Atom)} {a b : Ty Atom}
    {values : Expr Op Γ (.list a)} {initial : Expr Op Γ b} {body : Expr Op (a :: b :: Γ) b}
    (input : Layout w (Env base Γ)) (entry : Layout w (a.Value base)) (state : Layout w (b.Value base))
    (capacity : Nat) (countFits : capacity < 2 ^ w)
    (argFits : entry.representation.encoding.words + state.representation.encoding.words + input.representation.encoding.words < 2 ^ w)
    (frameFits : 1 + capacity * entry.representation.encoding.words + state.representation.encoding.words +
      2 * input.representation.encoding.words < 2 ^ w)
    {valueCode : Compilation P .unit hw values input (entry.boundedList capacity countFits (by omega))}
    {initialCode : Compilation P .unit hw initial input state}
    {bodyCode : Compilation P .unit hw body (FoldImplementation.bodyInput entry state input argFits) state}
    {valueBuffers initialBuffers bodyBuffers : Nat}
    (valuesEmitted : valueCode.Emits valueBuffers) (initialEmitted : initialCode.Emits initialBuffers)
    (bodyEmitted : bodyCode.Emits bodyBuffers)
    (valueFits : valueBuffers < 2 ^ w) (initialFits : max 2 initialBuffers + 1 < 2 ^ w)
    (bodyFits : bodyBuffers < 2 ^ w) :
    (Compilation.fold (P := P) (cost := .unit) (hw := hw) (Γ := Γ) (a := a) (b := b)
      input entry state capacity countFits argFits frameFits valueCode initialCode bodyCode).Emits
      (max (max 2 (max valueBuffers (max 2 initialBuffers + 1)) + 1) (max 2 bodyBuffers + 1)) := by
  obtain ⟨values, valuesEq, valuesBound⟩ := valuesEmitted
  obtain ⟨initial, initialEq, initialBound⟩ := initialEmitted
  obtain ⟨body, bodyEq, bodyBound⟩ := bodyEmitted
  obtain ⟨accumulator, accumulatorEq, accumulatorBound⟩ := initial.checkedPair_accept
    (Implementation.identity input (width_pos hw)) (by decide) hw initialBound (show (0 : Nat) ≤ 0 from le_rfl)
    (by omega) (by omega) (by omega) (by omega) (by omega)
  simp only [Nat.max_zero] at accumulatorBound
  obtain ⟨frame, frameEq, frameBound⟩ := values.checkedPair_accept accumulator (by decide) hw valuesBound accumulatorBound
    valueFits initialFits (by omega)
    (by change (1 + capacity * entry.representation.encoding.words) + input.representation.encoding.words < 2 ^ w; omega)
    (by change (1 + capacity * entry.representation.encoding.words) +
          (state.representation.encoding.words + input.representation.encoding.words) < 2 ^ w; omega)
  have bodyName : body.program.savedBuffer < 2 ^ w := by dsimp [Realizer.savedBuffer]; omega
  let loop := FoldImplementation.compile entry state input argFits body (by decide) hw bodyName capacity countFits frameFits
  have loopBound : loop.program.code.memBound ≤ max 2 bodyBuffers + 1 :=
    (ListFold.buffers body.program.code entry.representation.encoding.words state.representation.encoding.words
      input.representation.encoding.words capacity).trans (by omega)
  refine ⟨frame.then loop, ?_, max_le_max frameBound loopBound⟩
  dsimp only [Compilation.compile]
  refine Option.bind_eq_some_iff.mpr ⟨values, valuesEq, ?_⟩
  refine Option.bind_eq_some_iff.mpr ⟨initial, initialEq, ?_⟩
  refine Option.bind_eq_some_iff.mpr ⟨body, bodyEq, ?_⟩
  refine Option.bind_eq_some_iff.mpr ⟨accumulator, accumulatorEq, ?_⟩
  refine Option.bind_eq_some_iff.mpr ⟨frame, frameEq, ?_⟩
  exact dite_eq_left bodyName

end Signatures.Runtime.CaliperBackend.SourceExpression
