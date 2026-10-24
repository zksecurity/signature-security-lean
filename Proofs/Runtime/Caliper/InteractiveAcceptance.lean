import Proofs.Runtime.Caliper.InteractiveRetain
import Proofs.Runtime.Caliper.WordAcceptance

/-! Stored-word acceptance of generated interactive control. Saving a caller
requires a new buffer name beyond the callee footprint, so its width bound is
an explicit obligation even when all names in the callee fit individually.
-/

namespace Signatures.Runtime.CaliperBackend.Interactive

open Caliper

variable {w : Nat} {I : Type} {spec : OracleSpec I}

theorem dispatch_descriptionFits (port : Port w spec) (left right : Code w) (leftWords rightWords : Nat)
    (hw : 16 < 2 ^ w) (leftFits : (left.lower port).DescriptionFits) (rightFits : (right.lower port).DescriptionFits)
    (leftWidth : leftWords < 2 ^ w) (rightWidth : rightWords < 2 ^ w) :
    ((dispatch left right leftWords rightWords).lower port).DescriptionFits := by
  have positive := width_pos hw
  apply WordIO.Code.DescriptionFits.seq (w := w) hw
  · exact WordIO.Code.DescriptionFits.compute (code := (.memLoad 1 0 0 : Stmt w))
      (by simp [DescriptionFits, description]; omega)
  · apply WordIO.Code.DescriptionFits.branch (w := w) (condition := 1) hw (Nat.one_lt_two_pow positive.ne')
    · exact WordIO.Code.DescriptionFits.seq hw
        (.compute (selectSlice_descriptionFits 1 rightWords hw rightWidth)) rightFits
    · exact WordIO.Code.DescriptionFits.seq hw
        (.compute (selectSlice_descriptionFits 1 leftWords hw leftWidth)) leftFits

theorem retain_descriptionFits (port : Port w spec) (body : Code w) (buffer inputWords outputWords savedWords : Nat)
    (hw : 16 < 2 ^ w) (bodyFits : (body.lower port).DescriptionFits) (name : buffer < 2 ^ w)
    (inputWidth : inputWords < 2 ^ w) (savedWidth : savedWords < 2 ^ w)
    (outputWidth : outputWords + savedWords < 2 ^ w) :
    ((retain body buffer inputWords outputWords savedWords).lower port).DescriptionFits := by
  apply WordIO.Code.DescriptionFits.seq hw
  · apply WordIO.Code.DescriptionFits.compute
    exact DescriptionFits.seq (width_pos hw) (Retain.save_descriptionFits _ _ _ hw name savedWidth)
      (selectSlice_descriptionFits _ _ hw inputWidth)
  · apply WordIO.Code.DescriptionFits.seq hw bodyFits
    apply WordIO.Code.DescriptionFits.compute
    apply DescriptionFits.seq (width_pos hw)
    · apply Assembly.code_descriptionFits _ hw
      · simpa [Retain.restoreOperands, Assembly.reads_length] using outputWidth
      · intro operand member
        rcases List.mem_append.mp member with left | right
        · exact Assembly.reads_namesFit 0 0 _ (by positivity) operand left
        · exact Assembly.reads_namesFit buffer 0 _ name operand right
    · simp [DescriptionFits, description, name]; omega

theorem loop_descriptionFits (port : Port w spec) (body stop : Code w) (resultWords stateWords fuel : Nat)
    (hw : 16 < 2 ^ w) (bodyFits : (body.lower port).DescriptionFits) (stopFits : (stop.lower port).DescriptionFits)
    (resultWidth : resultWords < 2 ^ w) (stateWidth : stateWords < 2 ^ w) :
    ((loop body stop resultWords stateWords fuel).lower port).DescriptionFits := by
  induction fuel with
  | zero => exact stopFits
  | succ fuel ih =>
    apply WordIO.Code.DescriptionFits.seq hw bodyFits
    exact dispatch_descriptionFits port (.compute .skip) _ _ _ hw
      (.compute (by simp [DescriptionFits, description])) ih resultWidth stateWidth

end Signatures.Runtime.CaliperBackend.Interactive
