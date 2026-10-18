import Signatures.Runtime.Caliper.Realizer

/-! A small concrete instantiation: ordinary word bits are accessible, with
proved Caliper execution and exact time. The same instructions can inspect word
encodings of field/group elements; their mathematical types are not opaque handles.
-/

namespace Signatures.Runtime.CaliperBackend

open Caliper

variable {w : Nat}

def wordEncoding (w : Nat) : Encoding w (Word w) where
  words := 1
  encode value := [value]
  decode bytes := match bytes with | [value] => some value | _ => none
  encode_length _ := rfl
  decode_encode _ := rfl
  decode_length bytes value := by
    cases bytes with
    | nil => simp
    | cons head tail => cases tail <;> simp

def wordRepresentation (w : Nat) (hw : 0 < w) : Representation w (Word w) where
  encoding := wordEncoding w
  fits := Nat.one_lt_two_pow hw.ne'

/-- In-place complement of the represented word, using ordinary memory and bit
instructions. Register 1 is scratch; register 0 retains the zero offset. -/
def complementCode (w : Nat) : Stmt w :=
  .seq (.memLoad 1 0 0) (.seq (.un .not 1 1) (.memStore 0 0 1))

def complementRealizer (cost : CostModel) :
    Realizer cost (wordRepresentation 8 (by decide)) (wordRepresentation 8 (by decide))
      (fun value => ~~~value) where
  code := complementCode 8
  positive_width := by decide
  description_fits := by
    simp [DescriptionFits, complementCode, description]
    decide
  random_free := by trivial
  time _ := cost.memLoad + (cost.un .not + cost.memStore)
  net _ := 0
  workspace _ := 0
  correct tape value before represented := by
    have hz := represented.1
    have hb : before.bufs 0 = #[value] := by
      have := congrArg List.toArray represented.2.1
      simpa [wordRepresentation, wordEncoding] using this
    have hload : (before.regs 0).toNat < (before.bufs 0).size := by simp [hz, hb]
    let loaded := before.setReg 1 value
    let changed := loaded.setReg 1 (~~~value)
    let after := changed.setBuf 0 #[~~~value]
    have h₁ : Caliper.Exec cost tape (.memLoad 1 0 0) before loaded cost.memLoad 0 0 := by
      convert Caliper.Exec.memLoad (C := cost) (tape := tape) hload using 1
      simp [hz, hb, loaded]
    have h₂ : Caliper.Exec cost tape (.un .not 1 1) loaded changed (cost.un .not) 0 0 := by
      convert Caliper.Exec.un (C := cost) (tape := tape) (s := loaded) (op := .not)
        (d := 1) (a := 1) using 1
      simp [loaded, changed]
    have hstore : (changed.regs 0).toNat < (changed.bufs 0).size := by
      simp [changed, loaded, hz, hb]
    have h₃ : Caliper.Exec cost tape (.memStore 0 0 1) changed after cost.memStore 0 0 := by
      convert Caliper.Exec.memStore (C := cost) (tape := tape) (src := 1) hstore using 1
      simp [after, changed, loaded, hz, hb]
    have execution : Caliper.Exec cost tape (complementCode 8) before after
        (cost.memLoad + (cost.un .not + cost.memStore)) 0 0 := by
      simpa [complementCode] using Caliper.Exec.seq h₁ (Caliper.Exec.seq h₂ h₃)
    refine ⟨after, 0, 0, execution, ⟨?_, ?_, ?_, ?_⟩, le_rfl, le_rfl⟩
    · simp [after, changed, loaded, hz]
    · simp [after, wordRepresentation, wordEncoding]
    · exact execution.wellFormed_preserved represented.2.2.1
    · exact represented.2.2.2

end Signatures.Runtime.CaliperBackend
