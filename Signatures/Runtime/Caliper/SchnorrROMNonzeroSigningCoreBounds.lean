import Signatures.Runtime.Caliper.SchnorrROMNonzeroSigningCore
import Signatures.Runtime.Caliper.ImplementationMemory

/-! Time, stored-code, buffer-name and visited-memory bounds of the executed
nonzero signing suffix, derived compositionally from the local implementation:
every projection, pair, test, guarded dispatch and cache step contributes its
own proved bound. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.NonzeroSigning
open Caliper BoundedSource SchnorrROMTape
variable {w : Nat} {M F G : Type} (config : Signing.Enumerated.Configuration w M F G)

/-! ### Projection bounds -/

section Projections
theorem projGG_bounded : (projGG config).BoundedBy (16 * pw config) (52 * pw config + 14) := by
  have bound : (projGG config).BoundedBy (8 * (pw config + pw config)) (26 * (pw config + pw config) + 14) :=
    route_bounded config _ _ _ _ _ _ _ _
  exact bound.mono (by omega) (by omega)
theorem projAG_bounded : (projAG config).BoundedBy (8 * (sw config + pw config)) (26 * (sw config + pw config) + 14) :=
  route_bounded config _ _ _ _ _ _ _ _
theorem projZA_bounded : (projZA config).BoundedBy (16 * sw config) (52 * sw config + 14) := by
  have bound : (projZA config).BoundedBy (8 * (sw config + sw config)) (26 * (sw config + sw config) + 14) :=
    route_bounded config _ _ _ _ _ _ _ _
  exact bound.mono (by omega) (by omega)
theorem projRZ_bounded : (projRZ config).BoundedBy (8 * (pw config + sw config)) (26 * (pw config + sw config) + 14) :=
  route_bounded config _ _ _ _ _ _ _ _
theorem routeWork_bounded [DecidableEq M] [DecidableEq G] :
    (routeWork config).BoundedBy (8 * (tw config + mw config + 4 * pw config + 2 * sw config))
      (26 * (tw config + mw config + 4 * pw config + 2 * sw config) + 14) := by
  have bound : (routeWork config).BoundedBy (8 * config.handler.core.work.representation.encoding.words)
      (26 * config.handler.core.work.representation.encoding.words + 14) := route_bounded config _ _ _ _ _ _ _ _
  rw [work_words] at bound
  exact bound

theorem projGG_names (slots : Nat) : NamesAccounted (projGG config).program.code slots := route_names config _ _ _ _ _ _ _ _ slots
theorem projAG_names (slots : Nat) : NamesAccounted (projAG config).program.code slots := route_names config _ _ _ _ _ _ _ _ slots
theorem projZA_names (slots : Nat) : NamesAccounted (projZA config).program.code slots := route_names config _ _ _ _ _ _ _ _ slots
theorem projRZ_names (slots : Nat) : NamesAccounted (projRZ config).program.code slots := route_names config _ _ _ _ _ _ _ _ slots
theorem routeWork_names [DecidableEq M] [DecidableEq G] (slots : Nat) : NamesAccounted (routeWork config).program.code slots :=
  route_names config _ _ _ _ _ _ _ _ slots
end Projections

/-! ### Composite bounds -/

section Bounds
variable [Zero F] [SMul F G] [Sub G] [Add F] [DecidableEq M] [DecidableEq G]
    (ops : Handler.Operations config) (arith : Arithmetic config)
    {scaleTime scaleWords subTime subWords addTime addWords : Nat}
    (scaleBound : ops.scale.BoundedBy scaleTime scaleWords) (subBound : ops.sub.BoundedBy subTime subWords)
    (addBound : arith.add.BoundedBy addTime addWords)

/-- Time budget of the suffix: three scalings, two subtractions, one field
addition, the managed-cache programmer and linear copying in the width. -/
def timeBudget (scaleTime subTime addTime : Nat) : Nat :=
  3 * scaleTime + 2 * subTime + addTime + Signing.Cache.timeBudget config.handler.core + 1800 * config.handler.core.width + 50
/-- Stored-code budget of the suffix. -/
def codeBudget (scaleWords subWords addWords : Nat) : Nat :=
  3 * scaleWords + 2 * subWords + addWords + Signing.Cache.codeBudget config.handler.core + 6000 * config.handler.core.width + 2000

include scaleBound subBound addBound in
theorem bounded : (implementation config ops arith).BoundedBy
    (timeBudget config scaleTime subTime addTime) (codeBudget config scaleWords subWords addWords) := by
  have hW := width_eq config
  have hI := input_words config
  have hN := nzInput_words config
  have hFr := frame_words config
  have hFd := framed_words config
  have eP : config.handler.core.point.representation.encoding.words = pw config := rfl
  have eS : config.handler.core.scalar.representation.encoding.words = sw config := rfl
  have eA : config.handler.core.arithmetic.point.representation.encoding.words = pw config := rfl
  have eAP : config.handler.core.arithmetic.points.representation.encoding.words = pw config + pw config := rfl
  have eR : config.handler.core.reply.representation.encoding.words = pw config + sw config := rfl
  have input := Implementation.second_boundedBy config.handler.core.scalar config.handler.core.input config.sampler.wordFits
    (nzInput_fits config)
  have point := Signing.Arithmetic.point_bounded config.handler.core trivial ops.scale ops.sub
    ops.scaleNames.buffers ops.reserve scaleBound subBound
  have commitmentB : (commitment config ops).BoundedBy _ _ := input.then point
  have commitB := Implementation.pair_boundedBy (commitment config ops)
    (Implementation.identity (nzInput config) (width_pos config.sampler.wordFits)) config.sampler.wordFits
    (nameFits config ops arith _ ((commitment_buffers config ops arith).trans (by omega)))
    (nameFits config ops arith _ ((le_of_eq (identity_buffers config _)).trans (Nat.zero_le _)))
    (nzInput_duplicate config) (nzInput_middle config) (frame_fits config) commitmentB
    (Implementation.identity_boundedBy _ _)
  change (commit config ops arith).BoundedBy _ _ at commitB
  have firstB := Implementation.first_boundedBy config.handler.core.point (nzInput config) config.sampler.wordFits
    (frame_fits config)
  have argsB := Implementation.pair_boundedBy _ ((projGG config).then ops.sub) config.sampler.wordFits
    (nameFits config ops arith _ (by
      have := Implementation.first_buffers (cost := .unit) (by decide) config.handler.core.point (nzInput config)
        config.sampler.wordFits (frame_fits config)
      omega))
    (nameFits config ops arith _ (by
      have := projGG_buffers config
      have := ops.subNames.buffers
      change max _ _ ≤ _
      unfold slots; omega)) (frame_duplicate config) (frame_middle_point config) (points_fits config) firstB
    ((projGG_bounded config).then subBound)
  change (testArgs config ops arith).BoundedBy _ _ at argsB
  have testB : (test config ops arith).BoundedBy _ _ :=
    (argsB.then (EncodedEquality.implementation_boundedBy config.handler.core.point config.sampler.wordFits
      (points_fits config))).castFunction rfl
  have repairB := Implementation.pair_boundedBy ((projAG config).then ops.scale) ((projZA config).then arith.add)
    config.sampler.wordFits
    (nameFits config ops arith _ (by
      have := projAG_buffers config
      have := ops.scaleNames.buffers
      change max _ _ ≤ _
      unfold slots; omega))
    (nameFits config ops arith _ (by
      have := projZA_buffers config
      have := arith.addNames.buffers
      change max _ _ ≤ _
      unfold slots; omega))
    (frame_duplicate config) (frame_middle_point config) (reply_fits config)
    ((projAG_bounded config).then scaleBound) ((projZA_bounded config).then addBound)
  change (repair config ops arith).BoundedBy _ _ at repairB
  have guardedB : (guarded config ops arith).BoundedBy _ _ :=
    (GuardedBranch.implementation_boundedBy (hw := config.sampler.wordFits) (test config ops arith)
      (nameFits config ops arith _ ((test_buffers config ops arith).trans (by omega)))
      (frame_duplicate config) (frame_tag config)
      ((repair config ops arith).restrictInput (fun v => zeroTest v = true))
      ((projRZ config).restrictInput (fun v => zeroTest v = false))
      testB (repairB.restrictInput _) ((projRZ_bounded config).restrictInput _)).castFunction rfl
  have framedB := Implementation.pair_boundedBy (guarded config ops arith)
    (Implementation.identity (frame config) (width_pos config.sampler.wordFits)) config.sampler.wordFits
    (nameFits config ops arith _ ((guarded_buffers config ops arith).trans (by omega)))
    (nameFits config ops arith _ ((le_of_eq (identity_buffers config _)).trans (Nat.zero_le _)))
    (frame_duplicate config) (frame_middle_reply config) (framed_fits config) guardedB
    (Implementation.identity_boundedBy _ _)
  change (framedReply config ops arith).BoundedBy _ _ at framedB
  have whole := (((commitB.then framedB).then (routeWork_bounded config)).then
    (Signing.Cache.bounded config.handler.core)).castFunction (rfl : _ = value)
  apply whole.mono
  · simp only [eP, eS, eA, eAP, eR, hN, hFr, hFd, hI] at *
    unfold timeBudget
    omega
  · simp only [eP, eS, eA, eAP, eR, hN, hFr, hFd, hI] at *
    unfold codeBudget
    omega

theorem names (slotsNamed : Nat) (scaleNames : NamesAccounted ops.scale.program.code slotsNamed)
    (subNames : NamesAccounted ops.sub.program.code slotsNamed) (addNames : NamesAccounted arith.add.program.code slotsNamed) :
    NamesAccounted (implementation config ops arith).program.code (max 5 slotsNamed) := by
  have sc := scaleNames.mono (Nat.le_max_right 5 slotsNamed)
  have su := subNames.mono (Nat.le_max_right 5 slotsNamed)
  have ad := addNames.mono (Nat.le_max_right 5 slotsNamed)
  have pointN : NamesAccounted (commitment config ops).program.code (max 5 slotsNamed) :=
    (Implementation.second_names config.handler.core.scalar config.handler.core.input config.sampler.wordFits
      (nzInput_fits config) _).seq
      (((Signing.Arithmetic.arguments_names config.handler.core trivial _).seq
        (BLSResponse.pointArguments_names config.handler.core.arithmetic _ ops.scale sc ops.scaleNames.buffers ops.reserve)).seq su)
  have commitN : NamesAccounted (commit config ops arith).program.code (max 5 slotsNamed) :=
    Implementation.pair_names _ _ _ _ _ _ _ _ pointN (skip_names _)
  have argsN : NamesAccounted (testArgs config ops arith).program.code (max 5 slotsNamed) :=
    Implementation.pair_names _ _ _ _ _ _ _ _
      (Implementation.first_names config.handler.core.point (nzInput config) config.sampler.wordFits (frame_fits config) _)
      ((projGG_names config _).seq su)
  have testN : NamesAccounted (test config ops arith).program.code (max 5 slotsNamed) :=
    argsN.seq ((EncodedEquality.implementation_names .unit config.handler.core.point config.sampler.wordFits
      (points_fits config)).accounted.mono (Nat.le_max_left _ _))
  have repairN : NamesAccounted (repair config ops arith).program.code (max 5 slotsNamed) :=
    Implementation.pair_names _ _ _ _ _ _ _ _ ((projAG_names config _).seq sc) ((projZA_names config _).seq ad)
  have guardedN : NamesAccounted (guarded config ops arith).program.code (max 5 slotsNamed) :=
    GuardedBranch.implementation_names (hw := config.sampler.wordFits) (test config ops arith)
      (nameFits config ops arith _ ((test_buffers config ops arith).trans (by omega)))
      (frame_duplicate config) (frame_tag config)
      ((repair config ops arith).restrictInput (fun v => zeroTest v = true))
      ((projRZ config).restrictInput (fun v => zeroTest v = false)) testN repairN (projRZ_names config _)
  have framedN : NamesAccounted (framedReply config ops arith).program.code (max 5 slotsNamed) :=
    Implementation.pair_names _ _ _ _ _ _ _ _ guardedN (skip_names _)
  exact ((commitN.seq framedN).seq (routeWork_names config _)).seq
    ((Signing.Cache.names config.handler.core).mono (Nat.le_max_left _ _))

include scaleBound subBound addBound in
/-- Visited-memory bound of an actual execution of the suffix. -/
theorem resources (slotsNamed : Nat) (scaleNames : NamesAccounted ops.scale.program.code slotsNamed)
    (subNames : NamesAccounted ops.sub.program.code slotsNamed) (addNames : NamesAccounted arith.add.program.code slotsNamed)
    (tape : RandomTape w) (input : (nzInput config).Value) (before : State w)
    (holds : (nzInput config).representation.Holds input before) (registers buffers : Nat)
    (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers) :
    ∃ after net peak, Caliper.Exec .unit tape (implementation config ops arith).program.code before after
        ((implementation config ops arith).program.time input) net peak ∧
      config.handler.core.output.representation.Holds
        ⟨value input.val, (implementation config ops arith).preserves input.val input.property⟩ after ∧
      (implementation config ops arith).program.time input ≤ timeBudget config scaleTime subTime addTime ∧
      ∀ between, (Caliper.Reaches .unit tape (implementation config ops arith).program.code before between ∨ between = after) →
        RegisterBound between (max registers (registerSlots (implementation config ops arith).program.code)) ∧
        between.SupportBound (max buffers (implementation config ops arith).program.code.memBound) ∧ between.WellFormed ∧
        (staticWords (implementation config ops arith).program.code registers buffers : Int) +
          between.liveMem (max buffers (implementation config ops arith).program.code.memBound) ≤
            5 * codeBudget config scaleWords subWords addWords + 4 * max 5 slotsNamed + registers + 3 * buffers +
              before.liveMem buffers + timeBudget config scaleTime subTime addTime :=
  (bounded config ops arith scaleBound subBound addBound).memoryBound
    (names config ops arith slotsNamed scaleNames subNames addNames)
    tape input before holds registers buffers initialRegisters initialBuffers

end Bounds
end Signatures.Runtime.CaliperBackend.SchnorrROM.NonzeroSigning
