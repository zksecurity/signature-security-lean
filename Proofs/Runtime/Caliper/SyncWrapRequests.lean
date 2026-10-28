import Proofs.Runtime.Caliper.SyncWrapSlots

/-! Requests, modes and slot updates of the wrapper as executed implementations: injecting a
hash index or message into the shared request packet, a point into the reply packet, a
wrapper mode into the state's mode sum, and appending a hash slot. -/
namespace Signatures.Runtime.CaliperBackend.SyncWrap
open Caliper BoundedSource WeightedFull

variable {w : Nat} {K M G F PK A : Type} [Zero F] (core : Core w K M G F PK A)

namespace Core

/-! ## Packet representations, shared with the inner caller -/
abbrev uniformRep := (UniformQuery.port core.inner.randomBound core.service.evaluation.cache.wordFits core.inner.randomFits).request
abbrev uniformReply := (UniformQuery.port core.inner.randomBound core.service.evaluation.cache.wordFits core.inner.randomFits).reply
abbrev groupRep := WeightedCallerPackets.groupRequest core.service
abbrev uniformAll := Layout.all core.uniformRep
abbrev uniformReplyAll := Layout.all core.uniformReply
abbrev groupAll := Layout.all core.groupRep
abbrev requestAll : Layout w core.inner.good.Request := Layout.all core.requestRep
abbrev replyAll : Layout w core.inner.good.Reply := Layout.all core.replyRep

theorem groupFits : 1 + max core.keyAll.representation.encoding.words core.messageAll.representation.encoding.words < 2 ^ w :=
  core.groupRep.fits
theorem requestFits : 1 + max core.uniformAll.representation.encoding.words core.groupAll.representation.encoding.words < 2 ^ w :=
  core.requestRep.fits
theorem replyFits : 1 + max core.uniformReplyAll.representation.encoding.words core.pointAll.representation.encoding.words < 2 ^ w :=
  core.replyRep.fits

/-! ## Requests -/
def hashRequest (index : core.keyLayout.Value) : core.inner.good.Request := .inr (.inl index)
def signRequest (message : core.message.Value) : core.inner.good.Request := .inr (.inr message)
def randomRequest (n : Fin (core.inner.randomBound + 1)) : core.inner.good.Request := .inl n

def groupHash : Implementation .unit core.keyAll core.groupAll Sum.inl :=
  (Implementation.inl core.keyAll core.messageAll core.wordFits core.groupFits).then
    (Implementation.allSum' (a := core.keyLayout.representation) (b := core.message.representation) core.wordFits core.groupFits)
def groupSign : Implementation .unit core.messageAll core.groupAll Sum.inr :=
  (Implementation.inr core.keyAll core.messageAll core.wordFits core.groupFits).then
    (Implementation.allSum' (a := core.keyLayout.representation) (b := core.message.representation) core.wordFits core.groupFits)
def requestGroup : Implementation .unit core.groupAll core.requestAll Sum.inr :=
  (Implementation.inr core.uniformAll core.groupAll core.wordFits core.requestFits).then
    (Implementation.allSum' (a := core.uniformRep) (b := core.groupRep) core.wordFits core.requestFits)
def hashRequestImpl : Implementation .unit core.keyAll core.requestAll core.hashRequest :=
  (core.groupHash.then core.requestGroup).castFunction rfl
def signRequestImpl : Implementation .unit core.messageAll core.requestAll core.signRequest :=
  (core.groupSign.then core.requestGroup).castFunction rfl
def randomRequestImpl : Implementation .unit core.uniformAll core.requestAll core.randomRequest :=
  ((Implementation.inl core.uniformAll core.groupAll core.wordFits core.requestFits).then
    (Implementation.allSum' (a := core.uniformRep) (b := core.groupRep) core.wordFits core.requestFits)).castFunction rfl

/-- A point as a reply packet. -/
def pointReply : Implementation .unit core.pointAll core.replyAll (fun point => .inr point) :=
  ((Implementation.inr core.uniformReplyAll core.pointAll core.wordFits core.replyFits).then
    (Implementation.allSum' (a := core.uniformReply) (b := core.point.representation) core.wordFits core.replyFits)).castFunction rfl

/-! ## Modes -/
def modeReady : Implementation .unit core.stateAll core.mode Sum.inl :=
  Implementation.inl core.stateAll core.tail₁ core.wordFits core.mode.representation.fits
def modePreSign : Implementation .unit core.preSign core.mode (fun value => .inr (.inl value)) :=
  ((Implementation.inl core.preSign core.tail₂ core.wordFits core.tail₁.representation.fits).then
    (Implementation.inr core.stateAll core.tail₁ core.wordFits core.mode.representation.fits)).castFunction rfl
def modeAfter : Implementation .unit core.afterHash core.mode (fun value => .inr (.inr (.inl value))) :=
  (((Implementation.inl core.afterHash core.forgeryAll core.wordFits core.tail₂.representation.fits).then
    (Implementation.inr core.preSign core.tail₂ core.wordFits core.tail₁.representation.fits)).then
    (Implementation.inr core.stateAll core.tail₁ core.wordFits core.mode.representation.fits)).castFunction rfl
def modeFinal : Implementation .unit core.forgeryAll core.mode (fun value => .inr (.inr (.inr value))) :=
  (((Implementation.inr core.afterHash core.forgeryAll core.wordFits core.tail₂.representation.fits).then
    (Implementation.inr core.preSign core.tail₂ core.wordFits core.tail₁.representation.fits)).then
    (Implementation.inr core.stateAll core.tail₁ core.wordFits core.mode.representation.fits)).castFunction rfl

/-! ## Slots -/
/-- The attacker's own hash slot. -/
def _root_.Signatures.Runtime.CaliperBackend.SyncWrap.own (F : Type) : Unit ⊕ F := .inl ()
def ownEntry : Implementation .unit core.slots core.slotEntry (fun _ => own F) :=
  Implementation.constant core.slots core.slotEntry ⟨own F, trivial⟩ core.wordFits
theorem slots_fits : core.slots.representation.encoding.words + core.slots.representation.encoding.words < 2 ^ w := by
  rw [slots_words]; exact core.fits (by unfold width; omega)
theorem entrySlots_fits : core.slotEntry.representation.encoding.words + core.slots.representation.encoding.words < 2 ^ w :=
  core.appendInput_fits
/-- Append the attacker's own hash slot. -/
def ownSnoc : Implementation .unit core.slots core.slots (fun values => core.append (own F, values)) :=
  ((core.ownEntry.pair (Implementation.identity core.slots (width_pos core.wordFits)) (by decide) core.wordFits
    (core.ownEntry.savedBuffer_lt (n := 2) (Implementation.constant_buffers _ _ _ _) (core.fits (by unfold width; omega)))
    ((Implementation.identity core.slots _).savedBuffer_lt (n := 0) (Implementation.identity_buffers _) (core.fits (by unfold width; omega)))
    core.slots_fits core.entrySlots_fits core.entrySlots_fits).then core.snoc).castFunction rfl
theorem ownSnoc_buffers : core.ownSnoc.program.code.memBound ≤ 40 := by
  unfold ownSnoc
  refine (Implementation.castFunction_buffers _ _ (Implementation.then_buffers _ _
    (Implementation.pair_buffers _ _ _ _ _ _ _ _ (Implementation.constant_buffers _ _ _ _) (Implementation.identity_buffers _))
    core.snoc_buffers)).trans ?_
  omega
theorem keyed_fits : core.scalarAll.representation.encoding.words + core.slots.representation.encoding.words < 2 ^ w := by
  rw [slots_words, scalarAll_words]; exact core.fits (by unfold width; omega)
theorem keyed_dup : core.keyed.representation.encoding.words + core.keyed.representation.encoding.words < 2 ^ w := by
  rw [keyed_words]; exact core.fits (by unfold width; omega)
theorem keyed_mid : core.scalarAll.representation.encoding.words + core.keyed.representation.encoding.words < 2 ^ w := by
  rw [keyed_words, scalarAll_words]; exact core.fits (by unfold width; omega)
/-- Append the attacker's own hash slot beside the key. -/
def appendOwn : Implementation .unit core.keyed core.keyed (fun value => (value.1, core.append (own F, value.2))) :=
  (Implementation.first (by decide) core.scalarAll core.slots core.wordFits core.keyed_fits).pair
    ((Implementation.second (by decide) core.scalarAll core.slots core.wordFits core.keyed_fits).then core.ownSnoc) (by decide) core.wordFits
    ((Implementation.first _ _ _ _ _).savedBuffer_lt (n := 2) (Implementation.first_buffers _ _ _ _ _) (core.fits (by unfold width; omega)))
    (Implementation.savedBuffer_lt _ (n := max 2 40) (Implementation.then_buffers _ _ (Implementation.second_buffers _ _ _ _ _) core.ownSnoc_buffers)
      (core.fits (by unfold width; omega)))
    core.keyed_dup core.keyed_mid core.keyed_fits

/-! ## Bounds -/
theorem keyAll_words : core.keyAll.representation.encoding.words = core.keyLayout.representation.encoding.words := rfl
theorem groupRep_words : core.groupRep.encoding.words =
    1 + max core.keyLayout.representation.encoding.words core.message.representation.encoding.words := rfl
theorem requestRep_words : core.requestRep.encoding.words = 1 + max core.uniformRep.encoding.words core.groupRep.encoding.words := rfl
theorem replyRep_words : core.replyRep.encoding.words = 1 + max core.uniformReply.encoding.words core.point.representation.encoding.words := rfl
theorem uniformAll_words : core.uniformAll.representation.encoding.words = core.uniformRep.encoding.words := rfl
theorem groupAll_words : core.groupAll.representation.encoding.words = core.groupRep.encoding.words := rfl
theorem uniformReplyAll_words : core.uniformReplyAll.representation.encoding.words = core.uniformReply.encoding.words := rfl

/-- One request or reply injection costs at most this. -/
def packetTime : Nat := 8 * (core.groupRep.encoding.words + core.requestRep.encoding.words + core.replyRep.encoding.words)
def packetWords : Nat := 26 * (core.groupRep.encoding.words + core.requestRep.encoding.words + core.replyRep.encoding.words) + 40

theorem hashRequestImpl_boundedBy : core.hashRequestImpl.BoundedBy core.packetTime core.packetWords := by
  unfold hashRequestImpl groupHash requestGroup
  refine (Implementation.BoundedBy.castFunction (((Implementation.inl_boundedBy _ _ _ _).then (Implementation.view_boundedBy _ _ _)).then
    ((Implementation.inr_boundedBy _ _ _ _).then (Implementation.view_boundedBy _ _ _))) _).mono ?_ ?_
  all_goals
    have := core.keyAll_words; have := core.messageAll_words; have := core.groupRep_words; have := core.requestRep_words
    have := core.uniformAll_words; have := core.groupAll_words
    simp only [packetTime, packetWords]; omega
theorem signRequestImpl_boundedBy : core.signRequestImpl.BoundedBy core.packetTime core.packetWords := by
  unfold signRequestImpl groupSign requestGroup
  refine (Implementation.BoundedBy.castFunction (((Implementation.inr_boundedBy _ _ _ _).then (Implementation.view_boundedBy _ _ _)).then
    ((Implementation.inr_boundedBy _ _ _ _).then (Implementation.view_boundedBy _ _ _))) _).mono ?_ ?_
  all_goals
    have := core.keyAll_words; have := core.messageAll_words; have := core.groupRep_words; have := core.requestRep_words
    have := core.uniformAll_words; have := core.groupAll_words
    simp only [packetTime, packetWords]; omega
theorem randomRequestImpl_boundedBy : core.randomRequestImpl.BoundedBy core.packetTime core.packetWords := by
  unfold randomRequestImpl
  refine (Implementation.BoundedBy.castFunction ((Implementation.inl_boundedBy _ _ _ _).then (Implementation.view_boundedBy _ _ _)) _).mono ?_ ?_
  all_goals
    have := core.requestRep_words; have := core.uniformAll_words; have := core.groupAll_words
    simp only [packetTime, packetWords]; omega
theorem pointReply_boundedBy : core.pointReply.BoundedBy core.packetTime core.packetWords := by
  unfold pointReply
  refine (Implementation.BoundedBy.castFunction ((Implementation.inr_boundedBy _ _ _ _).then (Implementation.view_boundedBy _ _ _)) _).mono ?_ ?_
  all_goals
    have := core.replyRep_words; have := core.uniformReplyAll_words; have := core.pointAll_words
    simp only [packetTime, packetWords]; omega

theorem hashRequestImpl_names (slots : Nat) : NamesAccounted core.hashRequestImpl.program.code (slots + 3) :=
  ((Implementation.inl_names _ _ _ _).mono (by omega) |>.seq (Implementation.view_names _ _ _ _)).seq
    ((Implementation.inr_names _ _ _ _).mono (by omega) |>.seq (Implementation.view_names _ _ _ _))
theorem signRequestImpl_names (slots : Nat) : NamesAccounted core.signRequestImpl.program.code (slots + 3) :=
  ((Implementation.inr_names _ _ _ _).mono (by omega) |>.seq (Implementation.view_names _ _ _ _)).seq
    ((Implementation.inr_names _ _ _ _).mono (by omega) |>.seq (Implementation.view_names _ _ _ _))
theorem randomRequestImpl_names (slots : Nat) : NamesAccounted core.randomRequestImpl.program.code (slots + 3) :=
  (Implementation.inl_names _ _ _ _).mono (by omega) |>.seq (Implementation.view_names _ _ _ _)
theorem pointReply_names (slots : Nat) : NamesAccounted core.pointReply.program.code (slots + 3) :=
  (Implementation.inr_names _ _ _ _).mono (by omega) |>.seq (Implementation.view_names _ _ _ _)
theorem hashRequestImpl_buffers : core.hashRequestImpl.program.code.memBound ≤ 3 :=
  (Implementation.then_buffers _ _ (Implementation.then_buffers _ _ (Implementation.inl_buffers _ _ _ _) (Implementation.view_buffers _ _ _))
    (Implementation.then_buffers _ _ (Implementation.inr_buffers _ _ _ _) (Implementation.view_buffers _ _ _))).trans (by omega)
theorem signRequestImpl_buffers : core.signRequestImpl.program.code.memBound ≤ 3 :=
  (Implementation.then_buffers _ _ (Implementation.then_buffers _ _ (Implementation.inr_buffers _ _ _ _) (Implementation.view_buffers _ _ _))
    (Implementation.then_buffers _ _ (Implementation.inr_buffers _ _ _ _) (Implementation.view_buffers _ _ _))).trans (by omega)
theorem randomRequestImpl_buffers : core.randomRequestImpl.program.code.memBound ≤ 3 :=
  (Implementation.then_buffers _ _ (Implementation.inl_buffers _ _ _ _) (Implementation.view_buffers _ _ _)).trans (by omega)
theorem pointReply_buffers : core.pointReply.program.code.memBound ≤ 3 :=
  (Implementation.then_buffers _ _ (Implementation.inr_buffers _ _ _ _) (Implementation.view_buffers _ _ _)).trans (by omega)

/-- One mode injection costs at most this. -/
def modeTime : Nat := 24 * (3 + core.width)
def modeWords : Nat := 78 * (3 + core.width) + 48
theorem tail₂_words : core.tail₂.representation.encoding.words ≤ 1 + core.width := by
  have := core.stateAll_words; have := core.messageAll_words; have := core.pointAll_words; have := core.forgeryAll_words
  change 1 + max ((_ + _) + _) _ ≤ _; unfold width; omega
theorem tail₁_words : core.tail₁.representation.encoding.words ≤ 2 + core.width := by
  have := core.stateAll_words; have := core.messageAll_words; have := core.pointAll_words; have := core.forgeryAll_words
  change 1 + max (_ + _) (1 + max ((_ + _) + _) _) ≤ _; unfold width; omega
/-- Injections, bounded through one word count. -/
theorem inl_width {X Y : Type} (left : Layout w X) (right : Layout w Y)
    (fits : 1 + max left.representation.encoding.words right.representation.encoding.words < 2 ^ w) {n : Nat}
    (bound : 1 + max left.representation.encoding.words right.representation.encoding.words ≤ n) :
    (Implementation.inl left right core.wordFits fits).BoundedBy (8 * n) (26 * n + 14) :=
  (Implementation.inl_boundedBy left right core.wordFits fits).mono (by omega) (by omega)
theorem inr_width {X Y : Type} (left : Layout w X) (right : Layout w Y)
    (fits : 1 + max left.representation.encoding.words right.representation.encoding.words < 2 ^ w) {n : Nat}
    (bound : 1 + max left.representation.encoding.words right.representation.encoding.words ≤ n) :
    (Implementation.inr left right core.wordFits fits).BoundedBy (8 * n) (26 * n + 14) :=
  (Implementation.inr_boundedBy left right core.wordFits fits).mono (by omega) (by omega)
theorem mode_sum_words : 1 + max core.stateAll.representation.encoding.words core.tail₁.representation.encoding.words ≤ 3 + core.width :=
  core.mode_words
theorem tail₁_sum_words : 1 + max core.preSign.representation.encoding.words core.tail₂.representation.encoding.words ≤ 2 + core.width :=
  core.tail₁_words
theorem tail₂_sum_words : 1 + max core.afterHash.representation.encoding.words core.forgeryAll.representation.encoding.words ≤ 1 + core.width :=
  core.tail₂_words
theorem modeReady_boundedBy : core.modeReady.BoundedBy core.modeTime core.modeWords :=
  (core.inl_width _ _ _ core.mode_sum_words).mono (by simp only [modeTime]; omega) (by simp only [modeWords]; omega)
theorem modePreSign_boundedBy : core.modePreSign.BoundedBy core.modeTime core.modeWords := by
  unfold modePreSign
  refine (Implementation.BoundedBy.castFunction ((core.inl_width _ _ _ core.tail₁_sum_words).then
    (core.inr_width _ _ _ core.mode_sum_words)) _).mono ?_ ?_ <;> simp only [modeTime, modeWords] <;> omega
theorem modeAfter_boundedBy : core.modeAfter.BoundedBy core.modeTime core.modeWords := by
  unfold modeAfter
  refine (Implementation.BoundedBy.castFunction (((core.inl_width _ _ _ core.tail₂_sum_words).then
    (core.inr_width _ _ _ core.tail₁_sum_words)).then (core.inr_width _ _ _ core.mode_sum_words)) _).mono ?_ ?_ <;>
    simp only [modeTime, modeWords] <;> omega
theorem modeFinal_boundedBy : core.modeFinal.BoundedBy core.modeTime core.modeWords := by
  unfold modeFinal
  refine (Implementation.BoundedBy.castFunction (((core.inr_width _ _ _ core.tail₂_sum_words).then
    (core.inr_width _ _ _ core.tail₁_sum_words)).then (core.inr_width _ _ _ core.mode_sum_words)) _).mono ?_ ?_ <;>
    simp only [modeTime, modeWords] <;> omega
theorem modeReady_names (slots : Nat) : NamesAccounted core.modeReady.program.code (slots + 3) := (Implementation.inl_names _ _ _ _).mono (by omega)
theorem modePreSign_names (slots : Nat) : NamesAccounted core.modePreSign.program.code (slots + 3) :=
  ((Implementation.inl_names _ _ _ _).mono (by omega)).seq ((Implementation.inr_names _ _ _ _).mono (by omega))
theorem modeAfter_names (slots : Nat) : NamesAccounted core.modeAfter.program.code (slots + 3) :=
  (((Implementation.inl_names _ _ _ _).mono (by omega)).seq ((Implementation.inr_names _ _ _ _).mono (by omega))).seq
    ((Implementation.inr_names _ _ _ _).mono (by omega))
theorem modeFinal_names (slots : Nat) : NamesAccounted core.modeFinal.program.code (slots + 3) :=
  (((Implementation.inr_names _ _ _ _).mono (by omega)).seq ((Implementation.inr_names _ _ _ _).mono (by omega))).seq
    ((Implementation.inr_names _ _ _ _).mono (by omega))
theorem modeReady_buffers : core.modeReady.program.code.memBound ≤ 3 := Implementation.inl_buffers _ _ _ _
theorem modePreSign_buffers : core.modePreSign.program.code.memBound ≤ 3 :=
  (Implementation.then_buffers _ _ (Implementation.inl_buffers _ _ _ _) (Implementation.inr_buffers _ _ _ _)).trans (by omega)
theorem modeAfter_buffers : core.modeAfter.program.code.memBound ≤ 3 :=
  (Implementation.then_buffers _ _ (Implementation.then_buffers _ _ (Implementation.inl_buffers _ _ _ _) (Implementation.inr_buffers _ _ _ _))
    (Implementation.inr_buffers _ _ _ _)).trans (by omega)
theorem modeFinal_buffers : core.modeFinal.program.code.memBound ≤ 3 :=
  (Implementation.then_buffers _ _ (Implementation.then_buffers _ _ (Implementation.inr_buffers _ _ _ _) (Implementation.inr_buffers _ _ _ _))
    (Implementation.inr_buffers _ _ _ _)).trans (by omega)

/-- Appending the attacker's own slot beside the key costs at most this. -/
def appendTime : Nat := core.snocTime + 400 * (4 + core.width)
def appendWords : Nat := core.snocWords + 1400 * (4 + core.width) + 400
theorem ownSnoc_boundedBy : core.ownSnoc.BoundedBy (core.snocTime + 120 * (4 + core.width)) (core.snocWords + 400 * (4 + core.width) + 200) := by
  unfold ownSnoc
  refine (Implementation.BoundedBy.castFunction ((Implementation.pair_boundedBy _ _ _ _ _ _ _ _ (Implementation.constant_bounded _ _ _ _)
    (Implementation.identity_boundedBy _ _)).then core.snoc_boundedBy) _).mono ?_ ?_
  all_goals have := core.slots_words; have := core.slotEntry_words; unfold width at *; omega
theorem appendOwn_boundedBy : core.appendOwn.BoundedBy core.appendTime core.appendWords := by
  unfold appendOwn
  refine (Implementation.pair_boundedBy _ _ _ _ _ _ _ _ (Implementation.first_boundedBy _ _ _ _)
    ((Implementation.second_boundedBy _ _ _ _).then core.ownSnoc_boundedBy)).mono ?_ ?_
  all_goals
    have := core.slots_words; have := core.keyed_words; have := core.scalarAll_words
    have hk := core.keyed_words; unfold keyed at hk
    simp only [appendTime, appendWords]; unfold width at *; omega
theorem ownSnoc_names (slots : Nat) : NamesAccounted core.ownSnoc.program.code slots :=
  (Implementation.pair_names _ _ _ _ _ _ _ _ (Implementation.constant_names _ _ _ _ _) (Implementation.identity_names _ _)).seq (core.snoc_names slots)
theorem appendOwn_names (slots : Nat) : NamesAccounted core.appendOwn.program.code slots :=
  Implementation.pair_names _ _ _ _ _ _ _ _ (Implementation.first_names _ _ _ _ _)
    ((Implementation.second_names _ _ _ _ _).seq (core.ownSnoc_names slots))
theorem appendOwn_buffers : core.appendOwn.program.code.memBound ≤ 41 :=
  (Implementation.pair_buffers _ _ _ _ _ _ _ _ (Implementation.first_buffers _ _ _ _ _)
    (Implementation.then_buffers _ _ (Implementation.second_buffers _ _ _ _ _) core.ownSnoc_buffers)).trans (by omega)

end Core

end Signatures.Runtime.CaliperBackend.SyncWrap
