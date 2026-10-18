import Signatures.Runtime.Caliper.BufferBounds

/-! Bounds for direct pairing after the generated scratch names have been proved
to fit. The code is the same as the existing checked-pair compiler result. -/

namespace Signatures.Runtime.CaliperBackend.BoundedSource

open Caliper

variable {w : Nat} {A B D : Type} {input : Layout w A} {left : Layout w B} {right : Layout w D}
    {f : A → B} {g : A → D}
    (first : Implementation .unit input left f) (second : Implementation .unit input right g)
    (hw : 16 < 2 ^ w) (firstFits : first.program.savedBuffer < 2 ^ w) (secondFits : second.program.savedBuffer < 2 ^ w)
    (duplicateFits : input.representation.encoding.words + input.representation.encoding.words < 2 ^ w)
    (middleFits : left.representation.encoding.words + input.representation.encoding.words < 2 ^ w)
    (outputFits : left.representation.encoding.words + right.representation.encoding.words < 2 ^ w)

theorem Implementation.pair_boundedBy {firstTime firstWords secondTime secondWords : Nat}
    (firstBound : first.BoundedBy firstTime firstWords) (secondBound : second.BoundedBy secondTime secondWords) :
    (first.pair second (by decide) hw firstFits secondFits duplicateFits middleFits outputFits).BoundedBy
      (firstTime + secondTime + 52 * input.representation.encoding.words + 36 * left.representation.encoding.words +
        16 * right.representation.encoding.words)
      (firstWords + secondWords + 169 * input.representation.encoding.words + 117 * left.representation.encoding.words +
        52 * right.representation.encoding.words + 124) :=
  Implementation.checkedPair_boundedBy first second hw duplicateFits middleFits outputFits
    _ _ _ _ firstBound secondBound _
    (by simp only [Implementation.checkedPair, dite_eq_left firstFits, dite_eq_left secondFits])

theorem Implementation.pair_buffers {firstBuffers secondBuffers : Nat}
    (firstBound : first.program.code.memBound ≤ firstBuffers) (secondBound : second.program.code.memBound ≤ secondBuffers) :
    (first.pair second (by decide) hw firstFits secondFits duplicateFits middleFits outputFits).program.code.memBound ≤
      max 2 (max firstBuffers secondBuffers) + 1 :=
  (Pairing.buffers first.program second.program (by decide) hw firstFits secondFits duplicateFits middleFits outputFits).trans (by omega)

theorem Implementation.pair_names {slots : Nat}
    (firstBound : NamesAccounted first.program.code slots) (secondBound : NamesAccounted second.program.code slots) :
    NamesAccounted (first.pair second (by decide) hw firstFits secondFits duplicateFits middleFits outputFits).program.code slots :=
  Pairing.names first.program second.program (by decide) hw firstFits secondFits duplicateFits middleFits outputFits firstBound secondBound

end Signatures.Runtime.CaliperBackend.BoundedSource
