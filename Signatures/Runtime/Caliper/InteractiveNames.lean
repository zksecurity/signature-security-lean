import Signatures.Runtime.Caliper.WordResources
import Signatures.Runtime.Caliper.BufferBounds
import Signatures.Runtime.Caliper.InteractiveDescription

/-! Dense register and descriptor accounting across interactive calls. Generated
save/restore wrappers reserve one buffer beyond the lowered callee footprint.
Their name extent is bounded by primitive reservations plus generated code size. -/

namespace Signatures.Runtime.CaliperBackend

open Caliper

variable {w : Nat}

theorem selectSlice_registers (start count : Nat) : registerSlots (selectSlice (w := w) start count) ≤ 3 := by
  have first := (copySlice_names (w := w) 0 1 start count).1
  have second := (copySlice_names (w := w) 1 0 0 count).1
  simp only [selectSlice, registerSlots]
  omega

theorem Retain.prepare_names (buffer input saved : Nat) :
    registerSlots (Retain.prepare (w := w) buffer input saved) ≤ 3 ∧
      (Retain.prepare (w := w) buffer input saved).memBound ≤ max 2 (buffer + 1) := by
  have copy := copySlice_names (w := w) 0 buffer input saved
  have selected := selectSlice_registers (w := w) 0 input
  have buffers := selectSlice_buffers (w := w) 0 input
  simp only [Retain.prepare, Retain.save, registerSlots, Stmt.memBound]
  omega

theorem Retain.finish_names (buffer output saved : Nat) :
    registerSlots (Retain.finish (w := w) buffer output saved) ≤ 3 ∧
      (Retain.finish (w := w) buffer output saved).memBound ≤ max 2 (buffer + 1) := by
  have assembled := Assembly.code_names (Retain.restoreOperands (w := w) buffer output saved) (buffer + 1)
    (by
      simp only [Retain.restoreOperands, Assembly.sourcesBound_append]
      exact ⟨Assembly.sourcesBound_reads _ _ _ _ (by omega), Assembly.sourcesBound_reads _ _ _ _ (by omega)⟩)
  simp only [Retain.finish, registerSlots, Stmt.memBound]
  omega

namespace WordIO

structure NamesBound (code : Code w) (slots : Nat) : Prop where
  registers : code.registerSlots ≤ slots
  buffers : code.memBound ≤ slots

def NamesAccounted (code : Code w) (slots : Nat) : Prop := NamesBound code (slots + code.descriptionWords)

theorem NamesBound.accounted {code : Code w} {slots : Nat} (bound : NamesBound code slots) : NamesAccounted code slots :=
  ⟨bound.registers.trans (Nat.le_add_right _ _), bound.buffers.trans (Nat.le_add_right _ _)⟩

theorem NamesAccounted.mono {code : Code w} {small large : Nat} (bound : NamesAccounted code small) (larger : small ≤ large) :
    NamesAccounted code large :=
  ⟨bound.registers.trans (Nat.add_le_add_right larger _), bound.buffers.trans (Nat.add_le_add_right larger _)⟩

theorem NamesAccounted.compute {code : Stmt w} {slots : Nat} (bound : CaliperBackend.NamesAccounted code slots) :
    NamesAccounted (.compute code) slots := by
  rcases bound with ⟨registers, buffers⟩
  constructor <;> simp only [Code.registerSlots, Code.memBound, Code.descriptionWords_compute] <;> omega

theorem NamesAccounted.seq {first second : Code w} {slots : Nat}
    (left : NamesAccounted first slots) (right : NamesAccounted second slots) : NamesAccounted (.seq first second) slots := by
  rcases left with ⟨lr, lb⟩
  rcases right with ⟨rr, rb⟩
  constructor <;> simp only [Code.registerSlots, Code.memBound, Code.descriptionWords_seq] <;> omega

theorem NamesAccounted.branch {yes no : Code w} {slots : Nat}
    (left : NamesAccounted yes slots) (right : NamesAccounted no slots) : NamesAccounted (.branch 1 yes no) slots := by
  rcases left with ⟨lr, lb⟩
  rcases right with ⟨rr, rb⟩
  constructor <;> simp only [Code.registerSlots, Code.memBound, Code.descriptionWords_branch] <;> omega

end WordIO

namespace Interactive

variable {I : Type} {spec : OracleSpec I} (port : Port w spec)

theorem dispatch_names {left right : Code w} {slots : Nat}
    (leftNames : WordIO.NamesAccounted (left.lower port) slots) (rightNames : WordIO.NamesAccounted (right.lower port) slots)
    (leftWords rightWords : Nat) : WordIO.NamesAccounted ((dispatch left right leftWords rightWords).lower port) slots :=
  (WordIO.NamesAccounted.compute (loadTag_names slots)).seq
    (((WordIO.NamesAccounted.compute (selectSlice_names _ _ _)).seq rightNames).branch
      ((WordIO.NamesAccounted.compute (selectSlice_names _ _ _)).seq leftNames))

theorem retain_buffers (body : Code w) (input output saved : Nat) :
    ((retain body (savedBuffer port body) input output saved).lower port).memBound ≤ max 2 (body.lower port).memBound + 1 := by
  have prepared := (Retain.prepare_names (w := w) (savedBuffer port body) input saved).2
  have finished := (Retain.finish_names (w := w) (savedBuffer port body) output saved).2
  change max (Retain.prepare (w := w) (savedBuffer port body) input saved).memBound
    (max (body.lower port).memBound (Retain.finish (w := w) (savedBuffer port body) output saved).memBound) ≤ _
  dsimp only [savedBuffer] at prepared finished ⊢
  omega

theorem retain_names {body : Code w} {slots : Nat} (bound : WordIO.NamesAccounted (body.lower port) slots)
    (input output saved : Nat) :
    WordIO.NamesAccounted ((retain body (savedBuffer port body) input output saved).lower port) slots := by
  have prepared := Retain.prepare_names (w := w) (savedBuffer port body) input saved
  have finished := Retain.finish_names (w := w) (savedBuffer port body) output saved
  have words : (body.lower port).descriptionWords + 4 ≤
      ((retain body (savedBuffer port body) input output saved).lower port).descriptionWords := by
    simp only [retain, Code.lower, WordIO.Code.descriptionWords_seq, WordIO.Code.descriptionWords_compute]
    omega
  rcases bound with ⟨registers, buffers⟩
  constructor
  · change max (registerSlots (Retain.prepare (w := w) (savedBuffer port body) input saved))
      (max (body.lower port).registerSlots (registerSlots (Retain.finish (w := w) (savedBuffer port body) output saved))) ≤ _
    omega
  · have bounded := retain_buffers port body input output saved
    dsimp only [savedBuffer] at prepared finished
    omega

end Interactive
end Signatures.Runtime.CaliperBackend
