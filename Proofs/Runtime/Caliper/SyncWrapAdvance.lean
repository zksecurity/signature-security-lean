import Proofs.Runtime.Caliper.SyncWrapPost

/-! The wrapper's step. Forwarding (`ready`) runs the inner caller on the reply; before a signing
hash the reply must be a point, which starts the signing query; after it, the corrected point
goes to the inner caller; after the final hash the wrapped forgery is returned. A reply of the
wrong kind repeats the pending request. -/
namespace Signatures.Runtime.CaliperBackend.SyncWrap
open Caliper BoundedSource WeightedFull

variable {w : Nat} {Atom : Type} {base : Atom → Type} {key scalar : Ty Atom} {M G PK A : Type} [Zero (scalar.Value base)]
  (core : Core w (key.Value base) M G (scalar.Value base) PK A) (routines : Routines core) (caller : SharedCaller core.inner)

namespace Core

/-! ## Layouts -/
abbrev tailRest := core.keyed.prod core.replyAll (core.fits2 (core.le3 core.keyed_le) (core.le3 core.replyAll_le))
theorem tailRest_le : core.tailRest.representation.encoding.words ≤ 2 * core.bound :=
  (Layout.prod_le _ _ _ core.keyed_le core.replyAll_le).trans (by omega)
abbrev advanceInput := core.wrapper.prod core.replyAll (core.fits2 (core.le3 core.wrapper_le) (core.le3 core.replyAll_le))
theorem advanceInput_le : core.advanceInput.representation.encoding.words ≤ 2 * core.bound :=
  (Layout.prod_le _ _ _ core.wrapper_le core.replyAll_le).trans (by omega)
abbrev readyInput := core.stateAll.prod core.tailRest (core.fits2 (core.le3 core.stateAll_le) (by have := core.tailRest_le; omega))
abbrev tail₁Input := core.tail₁.prod core.tailRest (core.fits2 (core.le3 core.tail₁_le) (by have := core.tailRest_le; omega))
abbrev preSignInput := core.preSign.prod core.tailRest (core.fits2 (core.le3 core.preSign_le) (by have := core.tailRest_le; omega))
abbrev tail₂Input := core.tail₂.prod core.tailRest (core.fits2 (core.le3 core.tail₂_le) (by have := core.tailRest_le; omega))
abbrev afterInput := core.afterHash.prod core.tailRest (core.fits2 (core.le3 core.afterHash_le) (by have := core.tailRest_le; omega))
abbrev finalModeInput := core.forgeryAll.prod core.tailRest (core.fits2 (core.le3 core.forgeryAll_le) (by have := core.tailRest_le; omega))
theorem readyInput_le : core.readyInput.representation.encoding.words ≤ 3 * core.bound :=
  (Layout.prod_le _ _ _ core.stateAll_le core.tailRest_le).trans (by omega)
theorem tail₁Input_le : core.tail₁Input.representation.encoding.words ≤ 3 * core.bound :=
  (Layout.prod_le _ _ _ core.tail₁_le core.tailRest_le).trans (by omega)
theorem preSignInput_le : core.preSignInput.representation.encoding.words ≤ 3 * core.bound :=
  (Layout.prod_le _ _ _ core.preSign_le core.tailRest_le).trans (by omega)
theorem tail₂Input_le : core.tail₂Input.representation.encoding.words ≤ 3 * core.bound :=
  (Layout.prod_le _ _ _ core.tail₂_le core.tailRest_le).trans (by omega)
theorem afterInput_le : core.afterInput.representation.encoding.words ≤ 3 * core.bound :=
  (Layout.prod_le _ _ _ core.afterHash_le core.tailRest_le).trans (by omega)
theorem finalModeInput_le : core.finalModeInput.representation.encoding.words ≤ 3 * core.bound :=
  (Layout.prod_le _ _ _ core.forgeryAll_le core.tailRest_le).trans (by omega)
theorem tailRestFits : core.keyed.representation.encoding.words + core.replyAll.representation.encoding.words < 2 ^ w :=
  core.fits2 (core.le3 core.keyed_le) (core.le3 core.replyAll_le)
theorem wrapperReplyFits : core.wrapper.representation.encoding.words + core.replyAll.representation.encoding.words < 2 ^ w :=
  core.fits2 (core.le3 core.wrapper_le) (core.le3 core.replyAll_le)
theorem keyedModeFits : core.keyed.representation.encoding.words + core.mode.representation.encoding.words < 2 ^ w :=
  core.fits2 (core.le3 core.keyed_le) (core.le3 core.mode_le)
theorem modeTailFits : core.mode.representation.encoding.words + core.tailRest.representation.encoding.words < 2 ^ w :=
  core.fits2 (core.le3 core.mode_le) (by have := core.tailRest_le; omega)
/-- Move the mode in front of the key and the reply. -/
def reorderAdvance : Implementation .unit core.advanceInput (core.mode.prod core.tailRest core.modeTailFits)
    (fun value => (value.1.2, (value.1.1, value.2))) :=
  (((Implementation.first (by decide) core.wrapper core.replyAll core.wordFits core.wrapperReplyFits).then
      (Implementation.second (by decide) core.keyed core.mode core.wordFits core.keyedModeFits)).pair'
    (((Implementation.first (by decide) core.wrapper core.replyAll core.wordFits core.wrapperReplyFits).then
      (Implementation.first (by decide) core.keyed core.mode core.wordFits core.keyedModeFits)).pair'
      (Implementation.second (by decide) core.wrapper core.replyAll core.wordFits core.wrapperReplyFits) core.wordFits
      (Implementation.then_buffers _ _ (Implementation.first_buffers _ _ _ _ _) (Implementation.first_buffers _ _ _ _ _))
      (Implementation.second_buffers _ _ _ _ _) (core.room (by omega))
      (core.fits4' (by rw [Layout.prod_words]; have := core.wrapper_le; have := core.replyAll_le; omega) (core.le3 core.keyed_le)
        (core.le3 core.replyAll_le)))
    core.wordFits (Implementation.then_buffers _ _ (Implementation.first_buffers _ _ _ _ _) (Implementation.second_buffers _ _ _ _ _))
    (Implementation.pair'_buffers _ _ _ _ _ _ _) (core.room (by omega))
    (core.fits4' (by rw [Layout.prod_words]; have := core.wrapper_le; have := core.replyAll_le; omega) (core.le3 core.mode_le)
      (by rw [Layout.prod_words]; have := core.keyed_le; have := core.replyAll_le; omega))).castFunction rfl
theorem reorderAdvance_buffers : core.reorderAdvance.program.code.memBound ≤ 6 := by
  unfold reorderAdvance
  exact (Implementation.castFunction_buffers _ _ (Implementation.pair'_buffers _ _ _ _ _ _ _)).trans (by omega)

variable {A' : Type} (data : Layout w A') (dataLe : data.representation.encoding.words ≤ core.bound)
include dataLe in
theorem dataTailFits : data.representation.encoding.words + core.tailRest.representation.encoding.words < 2 ^ w :=
  core.fits2 (core.le3 dataLe) (by have := core.tailRest_le; omega)
include dataLe in
theorem dataKeyedFits : data.representation.encoding.words + core.keyed.representation.encoding.words < 2 ^ w :=
  core.fits2 (core.le3 dataLe) (core.le3 core.keyed_le)
/-- Pending data beside the key. -/
abbrev dataKeyed := data.prod core.keyed (core.dataKeyedFits data dataLe)
include dataLe in
theorem dataKeyed_le : (core.dataKeyed data dataLe).representation.encoding.words ≤ 2 * core.bound :=
  (Layout.prod_le _ _ _ dataLe core.keyed_le).trans (by omega)
include dataLe in
theorem replyDataFits : core.replyAll.representation.encoding.words + (core.dataKeyed data dataLe).representation.encoding.words < 2 ^ w :=
  core.fits2 (core.le3 core.replyAll_le) (by have := core.dataKeyed_le data dataLe; omega)
/-- The reply in front of the pending data and the key. -/
abbrev replyFirst := core.replyAll.prod (core.dataKeyed data dataLe) (core.replyDataFits data dataLe)
include dataLe in
theorem replyFirst_le : (core.replyFirst data dataLe).representation.encoding.words ≤ 3 * core.bound :=
  (Layout.prod_le _ _ _ core.replyAll_le (core.dataKeyed_le data dataLe)).trans (by omega)

/-- Bring the reply in front of pending data and the key. -/
def replyToFront : Implementation .unit (data.prod core.tailRest (core.dataTailFits data dataLe)) (core.replyFirst data dataLe)
    (fun value => (value.2.2, (value.1, value.2.1))) :=
  (((Implementation.second (by decide) data core.tailRest core.wordFits (core.dataTailFits data dataLe)).then
      (Implementation.second (by decide) core.keyed core.replyAll core.wordFits core.tailRestFits)).pair'
    ((Implementation.first (by decide) data core.tailRest core.wordFits (core.dataTailFits data dataLe)).pair'
      ((Implementation.second (by decide) data core.tailRest core.wordFits (core.dataTailFits data dataLe)).then
        (Implementation.first (by decide) core.keyed core.replyAll core.wordFits core.tailRestFits)) core.wordFits
      (Implementation.first_buffers _ _ _ _ _)
      (Implementation.then_buffers _ _ (Implementation.second_buffers _ _ _ _ _) (Implementation.first_buffers _ _ _ _ _)) (core.room (by omega))
      (core.fits4' (by rw [Layout.prod_words]; have := core.tailRest_le; omega) (core.le3 dataLe) (core.le3 core.keyed_le)))
    core.wordFits (Implementation.then_buffers _ _ (Implementation.second_buffers _ _ _ _ _) (Implementation.second_buffers _ _ _ _ _))
    (Implementation.pair'_buffers _ _ _ _ _ _ _) (core.room (by omega))
    (core.fits4' (by rw [Layout.prod_words]; have := core.tailRest_le; omega) (core.le3 core.replyAll_le)
      (by rw [Layout.prod_words]; have := core.keyed_le; omega))).castFunction rfl
theorem replyToFront_buffers : (core.replyToFront data dataLe).program.code.memBound ≤ 6 := by
  unfold replyToFront
  exact (Implementation.castFunction_buffers _ _ (Implementation.pair'_buffers _ _ _ _ _ _ _)).trans (by omega)

/-- Split the reply packet into the coins or the point. -/
def splitReply : Implementation .unit (core.replyFirst data dataLe)
      (distributeInput core.uniformReplyAll core.pointAll (core.dataKeyed data dataLe) core.wordFits
        (core.fitsSum3 (core.le3 core.uniformReplyAll_le) (core.le3 core.pointAll_le) (by have := core.dataKeyed_le data dataLe; omega)))
      (fun value => (value.1, value.2)) :=
  ((Implementation.first (by decide) core.replyAll (core.dataKeyed data dataLe) core.wordFits (core.replyDataFits data dataLe)).then
      (Implementation.allSum (a := core.uniformReply) (b := core.point.representation) core.wordFits core.replyFits)).pair'
    (Implementation.second (by decide) core.replyAll (core.dataKeyed data dataLe) core.wordFits (core.replyDataFits data dataLe)) core.wordFits
    (Implementation.then_buffers _ _ (Implementation.first_buffers _ _ _ _ _) (Implementation.view_buffers _ _ _))
    (Implementation.second_buffers _ _ _ _ _) (core.room (by omega))
    (core.fits4' (by rw [Layout.prod_words]; have := core.dataKeyed_le data dataLe; have := core.replyAll_le; omega)
      (core.le3 (by rw [Layout.sum_words, Layout.all_words, Layout.all_words]; have := core.replyRep_words; unfold bound width; omega))
      (by have := core.dataKeyed_le data dataLe; omega))
theorem splitReply_buffers : (core.splitReply data dataLe).program.code.memBound ≤ 3 :=
  (Implementation.pair'_buffers _ _ _ _ _ _ _).trans (by omega)

end Core

/-! ### Pieces shared by the mode branches -/
namespace Core
theorem innerStep_buffers : (core.innerStep caller).program.code.memBound ≤ max caller.continuation.code.memBound 3 :=
  (Implementation.castFunction_buffers _ _ (Implementation.then_buffers _ _ (Implementation.then_buffers _ _
    (Implementation.view_buffers _ _ _) (Implementation.ofRealizer_buffers _ le_rfl)) core.splitNext_buffers)).trans (by omega)
abbrev preKeyed := core.dataKeyed core.preSign core.preSign_le
theorem preKeyed_le : core.preKeyed.representation.encoding.words ≤ 2 * core.bound := core.dataKeyed_le core.preSign core.preSign_le
abbrev afterKeyed := core.dataKeyed core.afterHash core.afterHash_le
theorem afterKeyed_le : core.afterKeyed.representation.encoding.words ≤ 2 * core.bound := core.dataKeyed_le core.afterHash core.afterHash_le
abbrev sigInput := core.pointAll.prod core.afterKeyed (core.fits2 (core.le3 core.pointAll_le) (by have := core.afterKeyed_le; omega))
theorem sigInput_le : core.sigInput.representation.encoding.words ≤ 3 * core.bound :=
  (Layout.prod_le _ _ _ core.pointAll_le core.afterKeyed_le).trans (by omega)
theorem afterFits : (core.messageAll.prod core.pointAll (core.fits2 (core.le3 core.messageAll_le) (core.le3 core.pointAll_le))).representation.encoding.words +
    core.stateAll.representation.encoding.words < 2 ^ w :=
  core.fits2 (by rw [Layout.prod_words]; have := core.messageAll_le; have := core.pointAll_le; omega) (core.le3 core.stateAll_le)
/-- The pending signing data from a signature reply input. -/
def sigData : Implementation .unit core.sigInput core.afterHash (fun value => value.2.1) :=
  (Implementation.second (by decide) core.pointAll core.afterKeyed core.wordFits _).then
    (Implementation.first (by decide) core.afterHash core.keyed core.wordFits (core.dataKeyedFits core.afterHash core.afterHash_le))
theorem sigData_buffers : core.sigData.program.code.memBound ≤ 2 :=
  (Implementation.then_buffers _ _ (Implementation.second_buffers _ _ _ _ _) (Implementation.first_buffers _ _ _ _ _)).trans (by omega)
def sigKeyed : Implementation .unit core.sigInput core.keyed (fun value => value.2.2) :=
  (Implementation.second (by decide) core.pointAll core.afterKeyed core.wordFits _).then
    (Implementation.second (by decide) core.afterHash core.keyed core.wordFits (core.dataKeyedFits core.afterHash core.afterHash_le))
theorem sigKeyed_buffers : core.sigKeyed.program.code.memBound ≤ 2 :=
  (Implementation.then_buffers _ _ (Implementation.second_buffers _ _ _ _ _) (Implementation.second_buffers _ _ _ _ _)).trans (by omega)
def sigKey : Implementation .unit core.sigInput core.scalarAll (fun value => value.2.2.1) :=
  core.sigKeyed.then (Implementation.first (by decide) core.scalarAll core.slots core.wordFits core.keyed_fits)
theorem sigKey_buffers : core.sigKey.program.code.memBound ≤ 2 :=
  (Implementation.then_buffers _ _ core.sigKeyed_buffers (Implementation.first_buffers _ _ _ _ _)).trans (by omega)
def sigMessage : Implementation .unit core.sigInput core.messageAll (fun value => value.2.1.1.1) :=
  (core.sigData.then (Implementation.first (by decide) (core.messageAll.prod core.pointAll _) core.stateAll core.wordFits core.afterFits)).then
    (Implementation.first (by decide) core.messageAll core.pointAll core.wordFits _)
theorem sigMessage_buffers : core.sigMessage.program.code.memBound ≤ 2 :=
  (Implementation.then_buffers _ _ (Implementation.then_buffers _ _ core.sigData_buffers (Implementation.first_buffers _ _ _ _ _))
    (Implementation.first_buffers _ _ _ _ _)).trans (by omega)
def sigHash : Implementation .unit core.sigInput core.pointAll (fun value => value.2.1.1.2) :=
  (core.sigData.then (Implementation.first (by decide) (core.messageAll.prod core.pointAll _) core.stateAll core.wordFits core.afterFits)).then
    (Implementation.second (by decide) core.messageAll core.pointAll core.wordFits _)
theorem sigHash_buffers : core.sigHash.program.code.memBound ≤ 2 :=
  (Implementation.then_buffers _ _ (Implementation.then_buffers _ _ core.sigData_buffers (Implementation.first_buffers _ _ _ _ _))
    (Implementation.second_buffers _ _ _ _ _)).trans (by omega)
def sigState : Implementation .unit core.sigInput core.stateAll (fun value => value.2.1.2) :=
  core.sigData.then (Implementation.second (by decide) (core.messageAll.prod core.pointAll _) core.stateAll core.wordFits core.afterFits)
theorem sigState_buffers : core.sigState.program.code.memBound ≤ 2 :=
  (Implementation.then_buffers _ _ core.sigData_buffers (Implementation.second_buffers _ _ _ _ _)).trans (by omega)
/-- The correction scalar for the pending signing query. -/
def sigCorrection : Implementation .unit core.sigInput core.scalarAll (fun value => routines.corrFn (value.2.2.1, value.2.1.1.1)) :=
  (core.sigKey.pair' core.sigMessage core.wordFits core.sigKey_buffers core.sigMessage_buffers (core.room (by omega))
    (core.fits4' core.sigInput_le (core.le3 core.scalarAll_le) (core.le3 core.messageAll_le))).then routines.corr
theorem sigCorrection_buffers : (core.sigCorrection routines).program.code.memBound ≤ max routines.slots 3 :=
  (Implementation.then_buffers _ _ (Implementation.pair'_buffers _ _ _ _ _ _ _) routines.corrBuffers).trans (by omega)
/-- The period's hash beside the signature. -/
def sigPoints : Implementation .unit core.sigInput (core.pointAll.prod core.pointAll (core.fits2 (core.le3 core.pointAll_le) (core.le3 core.pointAll_le)))
    (fun value => (value.2.1.1.2, value.1)) :=
  core.sigHash.pair' (Implementation.first (by decide) core.pointAll core.afterKeyed core.wordFits _) core.wordFits core.sigHash_buffers
    (Implementation.first_buffers _ _ _ _ _) (core.room (by omega)) (core.fits4' core.sigInput_le (core.le3 core.pointAll_le) (core.le3 core.pointAll_le))
theorem sigPoints_buffers : core.sigPoints.program.code.memBound ≤ 3 := (Implementation.pair'_buffers _ _ _ _ _ _ _).trans (by omega)
/-- The corrected signature. -/
def sigCorrected : Implementation .unit core.sigInput core.pointAll
    (fun value => routines.fmaFn (routines.corrFn (value.2.2.1, value.2.1.1.1), (value.2.1.1.2, value.1))) :=
  ((core.sigCorrection routines).pair' core.sigPoints core.wordFits (core.sigCorrection_buffers routines) core.sigPoints_buffers
    (by have := routines.reserve; omega)
    (core.fits4' core.sigInput_le (core.le3 core.scalarAll_le) (by rw [Layout.prod_words]; have := core.pointAll_le; omega))).then routines.fma
theorem sigCorrected_buffers : (core.sigCorrected routines).program.code.memBound ≤ max routines.slots 3 + 1 :=
  (Implementation.then_buffers _ _ (Implementation.pair'_buffers _ _ _ _ _ _ _) routines.fmaBuffers).trans (by omega)
/-- The inner caller's next input: its state and the corrected signature as a reply. -/
def sigResume : Implementation .unit core.sigInput (core.stateAll.prod core.replyAll core.resumeFits)
    (fun value => (value.2.1.2, .inr (routines.fmaFn (routines.corrFn (value.2.2.1, value.2.1.1.1), (value.2.1.1.2, value.1))))) :=
  core.sigState.pair' ((core.sigCorrected routines).then core.pointReply) core.wordFits core.sigState_buffers
    (Implementation.then_buffers _ _ (core.sigCorrected_buffers routines) core.pointReply_buffers) (by have := routines.reserve; omega)
    (core.fits4' core.sigInput_le (core.le3 core.stateAll_le) (core.le3 core.replyAll_le))
theorem sigResume_buffers : (core.sigResume routines).program.code.memBound ≤ max routines.slots 3 + 2 :=
  (Implementation.pair'_buffers _ _ _ _ _ _ _).trans (by omega)

end Core

/-! ## The step -/
section Modes
variable (out : Layout w (M × (scalar.Value base × (List (scalar.Value base) × List (scalar.Value base)))))
  (outLe : out.representation.encoding.words ≤ core.outWords)

namespace Core

/-- Forwarding: run the inner caller on the reply and react. -/
def readyStep (callerReserve : caller.continuation.code.memBound + 50 < 2 ^ w) :
    Implementation .unit core.readyInput (core.output out outLe)
    (fun value => core.postFn routines (value.2.1, caller.advance (value.1, value.2.2))) :=
  ((((Implementation.second (by decide) core.stateAll core.tailRest core.wordFits (core.dataTailFits core.stateAll core.stateAll_le)).then
      (Implementation.first (by decide) core.keyed core.replyAll core.wordFits core.tailRestFits)).pair'
    (((Implementation.first (by decide) core.stateAll core.tailRest core.wordFits (core.dataTailFits core.stateAll core.stateAll_le)).pair'
      ((Implementation.second (by decide) core.stateAll core.tailRest core.wordFits (core.dataTailFits core.stateAll core.stateAll_le)).then
        (Implementation.second (by decide) core.keyed core.replyAll core.wordFits core.tailRestFits)) core.wordFits
      (Implementation.first_buffers _ _ _ _ _)
      (Implementation.then_buffers _ _ (Implementation.second_buffers _ _ _ _ _) (Implementation.second_buffers _ _ _ _ _)) (core.room (by omega))
      (core.fits4' core.readyInput_le (core.le3 core.stateAll_le) (core.le3 core.replyAll_le))).then (core.innerStep caller)) core.wordFits
    (Implementation.then_buffers _ _ (Implementation.second_buffers _ _ _ _ _) (Implementation.first_buffers _ _ _ _ _))
    (Implementation.then_buffers _ _ (Implementation.pair'_buffers _ _ _ _ _ _ _) (core.innerStep_buffers caller))
    (by have := callerReserve; omega)
    (core.fits4' core.readyInput_le (core.le3 core.keyed_le) (core.le3 core.nextSplit_le))).then
    (core.post routines out outLe)).castFunction rfl

/-! ### Before the signing hash -/
/-- The reply was coins: repeat the hash request. -/
def preSignMismatch : Implementation .unit (core.uniformReplyAll.prod core.preKeyed
      (core.fits2 (core.le3 core.uniformReplyAll_le) (by have := core.preKeyed_le; omega)))
    (core.output out outLe)
    (fun value => .inr (core.hashRequest (routines.hashOfFn value.2.1.1), (value.2.2, .inr (.inl value.2.1)))) :=
  (((((((Implementation.second (by decide) core.uniformReplyAll core.preKeyed core.wordFits _).then
        (Implementation.first (by decide) core.preSign core.keyed core.wordFits _)).then
        (Implementation.first (by decide) core.messageAll core.stateAll core.wordFits _)).then routines.hashOf).then core.hashRequestImpl).pair'
    (((Implementation.second (by decide) core.uniformReplyAll core.preKeyed core.wordFits _).then
        (Implementation.second (by decide) core.preSign core.keyed core.wordFits _)).pair'
      (((Implementation.second (by decide) core.uniformReplyAll core.preKeyed core.wordFits _).then
        (Implementation.first (by decide) core.preSign core.keyed core.wordFits _)).then core.modePreSign) core.wordFits
      (Implementation.then_buffers _ _ (Implementation.second_buffers _ _ _ _ _) (Implementation.second_buffers _ _ _ _ _))
      (Implementation.then_buffers _ _ (Implementation.then_buffers _ _ (Implementation.second_buffers _ _ _ _ _) (Implementation.first_buffers _ _ _ _ _))
        core.modePreSign_buffers) (core.room (by omega))
      (core.fits4' (by rw [Layout.prod_words]; rw [Layout.prod_words]; have := core.uniformReplyAll_le; have := core.preSign_le; have := core.keyed_le; omega)
        (core.le3 core.keyed_le) (core.le3 core.mode_le))) core.wordFits
    (Implementation.then_buffers _ _ (Implementation.then_buffers _ _ (Implementation.then_buffers _ _ (Implementation.then_buffers _ _
      (Implementation.second_buffers _ _ _ _ _) (Implementation.first_buffers _ _ _ _ _)) (Implementation.first_buffers _ _ _ _ _))
      routines.hashOfBuffers) core.hashRequestImpl_buffers)
    (Implementation.pair'_buffers _ _ _ _ _ _ _) (by have := routines.reserve; omega)
    (core.fits4' (by rw [Layout.prod_words]; rw [Layout.prod_words]; have := core.uniformReplyAll_le; have := core.preSign_le; have := core.keyed_le; omega)
      (core.le3 core.requestAll_le) (core.le3 core.wrapper_le))).then
    (Implementation.inr out core.pendingWrapper core.wordFits (core.outputFits out outLe))).castFunction rfl
/-- The reply was the period's hash: issue the signing query. -/
def preSignHash : Implementation .unit (core.pointAll.prod core.preKeyed
      (core.fits2 (core.le3 core.pointAll_le) (by have := core.preKeyed_le; omega)))
    (core.output out outLe)
    (fun value => .inr (core.signRequest value.2.1.1, (value.2.2, .inr (.inr (.inl ((value.2.1.1, value.1), value.2.1.2)))))) :=
  ((((((Implementation.second (by decide) core.pointAll core.preKeyed core.wordFits _).then
        (Implementation.first (by decide) core.preSign core.keyed core.wordFits _)).then
        (Implementation.first (by decide) core.messageAll core.stateAll core.wordFits _)).then core.signRequestImpl).pair'
    (((Implementation.second (by decide) core.pointAll core.preKeyed core.wordFits _).then
        (Implementation.second (by decide) core.preSign core.keyed core.wordFits _)).pair'
      ((((((Implementation.second (by decide) core.pointAll core.preKeyed core.wordFits _).then
          (Implementation.first (by decide) core.preSign core.keyed core.wordFits _)).then
          (Implementation.first (by decide) core.messageAll core.stateAll core.wordFits _)).pair'
        (Implementation.first (by decide) core.pointAll core.preKeyed core.wordFits _) core.wordFits
        (Implementation.then_buffers _ _ (Implementation.then_buffers _ _ (Implementation.second_buffers _ _ _ _ _) (Implementation.first_buffers _ _ _ _ _))
          (Implementation.first_buffers _ _ _ _ _)) (Implementation.first_buffers _ _ _ _ _) (core.room (by omega))
        (core.fits4' (by rw [Layout.prod_words]; rw [Layout.prod_words]; have := core.pointAll_le; have := core.preSign_le; have := core.keyed_le; omega)
          (core.le3 core.messageAll_le) (core.le3 core.pointAll_le))).pair'
        (((Implementation.second (by decide) core.pointAll core.preKeyed core.wordFits _).then
          (Implementation.first (by decide) core.preSign core.keyed core.wordFits _)).then
          (Implementation.second (by decide) core.messageAll core.stateAll core.wordFits _)) core.wordFits
        (Implementation.pair'_buffers _ _ _ _ _ _ _)
        (Implementation.then_buffers _ _ (Implementation.then_buffers _ _ (Implementation.second_buffers _ _ _ _ _) (Implementation.first_buffers _ _ _ _ _))
          (Implementation.second_buffers _ _ _ _ _)) (core.room (by omega))
        (core.fits4' (by rw [Layout.prod_words]; rw [Layout.prod_words]; have := core.pointAll_le; have := core.preSign_le; have := core.keyed_le; omega)
          (by rw [Layout.prod_words]; have := core.messageAll_le; have := core.pointAll_le; omega) (core.le3 core.stateAll_le))).then
        core.modeAfter) core.wordFits
      (Implementation.then_buffers _ _ (Implementation.second_buffers _ _ _ _ _) (Implementation.second_buffers _ _ _ _ _))
      (Implementation.then_buffers _ _ (Implementation.pair'_buffers _ _ _ _ _ _ _) core.modeAfter_buffers) (core.room (by omega))
      (core.fits4' (by rw [Layout.prod_words]; rw [Layout.prod_words]; have := core.pointAll_le; have := core.preSign_le; have := core.keyed_le; omega)
        (core.le3 core.keyed_le) (core.le3 core.mode_le))) core.wordFits
    (Implementation.then_buffers _ _ (Implementation.then_buffers _ _ (Implementation.then_buffers _ _ (Implementation.second_buffers _ _ _ _ _)
      (Implementation.first_buffers _ _ _ _ _)) (Implementation.first_buffers _ _ _ _ _)) core.signRequestImpl_buffers)
    (Implementation.pair'_buffers _ _ _ _ _ _ _) (core.room (by omega))
    (core.fits4' (by rw [Layout.prod_words]; rw [Layout.prod_words]; have := core.pointAll_le; have := core.preSign_le; have := core.keyed_le; omega)
      (core.le3 core.requestAll_le) (core.le3 core.wrapper_le))).then
    (Implementation.inr out core.pendingWrapper core.wordFits (core.outputFits out outLe))).castFunction rfl
/-- Before the signing hash. -/
def preSignReact : Implementation .unit core.preSignInput (core.output out outLe)
    (fun value => match value.2.2 with
      | .inl _ => .inr (core.hashRequest (routines.hashOfFn value.1.1), (value.2.1, .inr (.inl value.1)))
      | .inr point => .inr (core.signRequest value.1.1, (value.2.1, .inr (.inr (.inl ((value.1.1, point), value.1.2)))))) :=
  ((((core.replyToFront core.preSign core.preSign_le).then (core.splitReply core.preSign core.preSign_le)).then
    (Implementation.distribute core.uniformReplyAll core.pointAll core.preKeyed core.wordFits _)).then
    (Implementation.branch (core.preSignMismatch routines out outLe) (core.preSignHash out outLe) (by decide) core.wordFits
      (core.fitsSum (by rw [Layout.prod_words]; rw [Layout.prod_words]; have := core.uniformReplyAll_le; have := core.preSign_le; have := core.keyed_le; omega)
        (by rw [Layout.prod_words]; rw [Layout.prod_words]; have := core.pointAll_le; have := core.preSign_le; have := core.keyed_le; omega)))).castFunction (by
      funext value
      rcases value with ⟨data, keyed, coins | point⟩ <;> rfl)

/-! ### After the signing hash -/
/-- The reply was coins: repeat the signing request. -/
def afterMismatch : Implementation .unit (core.uniformReplyAll.prod core.afterKeyed
      (core.fits2 (core.le3 core.uniformReplyAll_le) (by have := core.afterKeyed_le; omega)))
    (core.output out outLe)
    (fun value => .inr (core.signRequest value.2.1.1.1, (value.2.2, .inr (.inr (.inl value.2.1))))) :=
  (((((((Implementation.second (by decide) core.uniformReplyAll core.afterKeyed core.wordFits _).then
        (Implementation.first (by decide) core.afterHash core.keyed core.wordFits _)).then
        (Implementation.first (by decide) (core.messageAll.prod core.pointAll _) core.stateAll core.wordFits _)).then
        (Implementation.first (by decide) core.messageAll core.pointAll core.wordFits _)).then core.signRequestImpl).pair'
    (((Implementation.second (by decide) core.uniformReplyAll core.afterKeyed core.wordFits _).then
        (Implementation.second (by decide) core.afterHash core.keyed core.wordFits _)).pair'
      (((Implementation.second (by decide) core.uniformReplyAll core.afterKeyed core.wordFits _).then
        (Implementation.first (by decide) core.afterHash core.keyed core.wordFits _)).then core.modeAfter) core.wordFits
      (Implementation.then_buffers _ _ (Implementation.second_buffers _ _ _ _ _) (Implementation.second_buffers _ _ _ _ _))
      (Implementation.then_buffers _ _ (Implementation.then_buffers _ _ (Implementation.second_buffers _ _ _ _ _) (Implementation.first_buffers _ _ _ _ _))
        core.modeAfter_buffers) (core.room (by omega))
      (core.fits4' (by rw [Layout.prod_words, Layout.prod_words]; have := core.uniformReplyAll_le; have := core.afterHash_le; have := core.keyed_le; omega)
        (core.le3 core.keyed_le) (core.le3 core.mode_le))) core.wordFits
    (Implementation.then_buffers _ _ (Implementation.then_buffers _ _ (Implementation.then_buffers _ _ (Implementation.then_buffers _ _
      (Implementation.second_buffers _ _ _ _ _) (Implementation.first_buffers _ _ _ _ _)) (Implementation.first_buffers _ _ _ _ _))
      (Implementation.first_buffers _ _ _ _ _)) core.signRequestImpl_buffers)
    (Implementation.pair'_buffers _ _ _ _ _ _ _) (core.room (by omega))
    (core.fits4' (by rw [Layout.prod_words, Layout.prod_words]; have := core.uniformReplyAll_le; have := core.afterHash_le; have := core.keyed_le; omega)
      (core.le3 core.requestAll_le) (core.le3 core.wrapper_le))).then
    (Implementation.inr out core.pendingWrapper core.wordFits (core.outputFits out outLe))).castFunction rfl

/-- The reply was the signature: correct it and resume the inner caller. -/
def afterSig (callerReserve : caller.continuation.code.memBound + 50 < 2 ^ w) :
    Implementation .unit core.sigInput (core.output out outLe)
      (fun value => core.postFn routines (value.2.2, caller.advance (value.2.1.2,
        .inr (routines.fmaFn (routines.corrFn (value.2.2.1, value.2.1.1.1), (value.2.1.1.2, value.1)))))) :=
  ((core.sigKeyed.pair' ((core.sigResume routines).then (core.innerStep caller)) core.wordFits core.sigKeyed_buffers
    (Implementation.then_buffers _ _ (core.sigResume_buffers routines) (core.innerStep_buffers caller))
    (by have := routines.reserve; omega)
    (core.fits4' core.sigInput_le (core.le3 core.keyed_le) (core.le3 core.nextSplit_le))).then
    (core.post routines out outLe)).castFunction rfl

/-- After the signing hash. -/
def afterReact (callerReserve : caller.continuation.code.memBound + 50 < 2 ^ w) :
    Implementation .unit core.afterInput (core.output out outLe)
    (fun value => match value.2.2 with
      | .inl _ => .inr (core.signRequest value.1.1.1, (value.2.1, .inr (.inr (.inl value.1))))
      | .inr point => core.postFn routines (value.2.1, caller.advance (value.1.2,
          .inr (routines.fmaFn (routines.corrFn (value.2.1.1, value.1.1.1), (value.1.1.2, point)))))) :=
  ((((core.replyToFront core.afterHash core.afterHash_le).then (core.splitReply core.afterHash core.afterHash_le)).then
    (Implementation.distribute core.uniformReplyAll core.pointAll core.afterKeyed core.wordFits _)).then
    (Implementation.branch (core.afterMismatch out outLe) (core.afterSig routines caller out outLe callerReserve) (by decide) core.wordFits
      (core.fitsSum (by rw [Layout.prod_words]; have := core.uniformReplyAll_le; have := core.afterKeyed_le; omega)
        (by rw [Layout.prod_words]; have := core.pointAll_le; have := core.afterKeyed_le; omega)))).castFunction (by
      funext value
      rcases value with ⟨data, keyed, coins | point⟩ <;> rfl)

end Core
end Modes

/-! ## Finishing, and the whole step -/
section Finish
variable (out : Layout w (M × (scalar.Value base × (List (scalar.Value base) × List (scalar.Value base)))))
  (outLe : out.representation.encoding.words ≤ core.outWords)
  {finishFn : core.forgeryIn.Value × (core.scalar.Value × List (Unit ⊕ scalar.Value base)) →
    M × (scalar.Value base × (List (scalar.Value base) × List (scalar.Value base)))}
  (finish : Implementation .unit core.finalInput out finishFn)

namespace Core

/-- After the final hash: return the wrapped forgery. -/
def finalModeReact :
    Implementation .unit core.finalModeInput (core.output out outLe) (fun value => .inl (finishFn (value.1, value.2.1))) :=
  ((((Implementation.first (by decide) core.forgeryAll core.tailRest core.wordFits (core.dataTailFits core.forgeryAll core.forgeryAll_le)).pair'
    ((Implementation.second (by decide) core.forgeryAll core.tailRest core.wordFits (core.dataTailFits core.forgeryAll core.forgeryAll_le)).then
      (Implementation.first (by decide) core.keyed core.replyAll core.wordFits core.tailRestFits)) core.wordFits
    (Implementation.first_buffers _ _ _ _ _)
    (Implementation.then_buffers _ _ (Implementation.second_buffers _ _ _ _ _) (Implementation.first_buffers _ _ _ _ _)) (core.room (by omega))
    (core.fits4' core.finalModeInput_le (core.le3 core.forgeryAll_le) (core.le3 core.keyed_le))).then finish).then
    (Implementation.inl out core.pendingWrapper core.wordFits (core.outputFits out outLe))).castFunction rfl

/-- The modes after a signing request was announced. -/
def tail₂React (callerReserve : caller.continuation.code.memBound + 50 < 2 ^ w) :
    Implementation .unit core.tail₂Input (core.output out outLe)
    (fun value => match value.1 with
      | .inl pending => match value.2.2 with
        | .inl _ => .inr (core.signRequest pending.1.1, (value.2.1, .inr (.inr (.inl pending))))
        | .inr point => core.postFn routines (value.2.1, caller.advance (pending.2,
            .inr (routines.fmaFn (routines.corrFn (value.2.1.1, pending.1.1), (pending.1.2, point)))))
      | .inr forged => .inl (finishFn (forged, value.2.1))) :=
  ((Implementation.distribute core.afterHash core.forgeryAll core.tailRest core.wordFits
      (core.fitsSum3 (core.le3 core.afterHash_le) (core.le3 core.forgeryAll_le) (by have := core.tailRest_le; omega))).then
    (Implementation.branch (core.afterReact routines caller out outLe callerReserve)
      (core.finalModeReact out outLe finish) (by decide) core.wordFits
      (core.fitsSum core.afterInput_le core.finalModeInput_le))).castFunction (by
      funext value
      rcases value with ⟨pending | forged, keyed, coins | point⟩ <;> rfl)

/-- The modes other than forwarding. -/
def tail₁React (callerReserve : caller.continuation.code.memBound + 50 < 2 ^ w) :
    Implementation .unit core.tail₁Input (core.output out outLe)
    (fun value => match value.1 with
      | .inl pending => match value.2.2 with
        | .inl _ => .inr (core.hashRequest (routines.hashOfFn pending.1), (value.2.1, .inr (.inl pending)))
        | .inr point => .inr (core.signRequest pending.1, (value.2.1, .inr (.inr (.inl ((pending.1, point), pending.2)))))
      | .inr (.inl pending) => match value.2.2 with
        | .inl _ => .inr (core.signRequest pending.1.1, (value.2.1, .inr (.inr (.inl pending))))
        | .inr point => core.postFn routines (value.2.1, caller.advance (pending.2,
            .inr (routines.fmaFn (routines.corrFn (value.2.1.1, pending.1.1), (pending.1.2, point)))))
      | .inr (.inr forged) => .inl (finishFn (forged, value.2.1))) :=
  ((Implementation.distribute core.preSign core.tail₂ core.tailRest core.wordFits
      (core.fitsSum3 (core.le3 core.preSign_le) (core.le3 core.tail₂_le) (by have := core.tailRest_le; omega))).then
    (Implementation.branch (core.preSignReact routines out outLe)
      (core.tail₂React routines caller out outLe finish callerReserve) (by decide) core.wordFits
      (core.fitsSum core.preSignInput_le core.tail₂Input_le))).castFunction (by
      funext value
      rcases value with ⟨pending | pending | forged, keyed, coins | point⟩ <;> rfl)

/-- The wrapper's step, as a function. -/
def advanceFn (value : ((core.scalar.Value × List (Unit ⊕ scalar.Value base)) ×
      (A ⊕ ((core.message.Value × A) ⊕ (((core.message.Value × core.point.Value) × A) ⊕ core.forgeryIn.Value)))) × core.inner.good.Reply) :
    (M × (scalar.Value base × (List (scalar.Value base) × List (scalar.Value base)))) ⊕
      (core.inner.good.Request × ((core.scalar.Value × List (Unit ⊕ scalar.Value base)) ×
        (A ⊕ ((core.message.Value × A) ⊕ (((core.message.Value × core.point.Value) × A) ⊕ core.forgeryIn.Value))))) :=
  match value.1.2 with
  | .inl state => core.postFn routines (value.1.1, caller.advance (state, value.2))
  | .inr (.inl pending) => match value.2 with
    | .inl _ => .inr (core.hashRequest (routines.hashOfFn pending.1), (value.1.1, .inr (.inl pending)))
    | .inr point => .inr (core.signRequest pending.1, (value.1.1, .inr (.inr (.inl ((pending.1, point), pending.2)))))
  | .inr (.inr (.inl pending)) => match value.2 with
    | .inl _ => .inr (core.signRequest pending.1.1, (value.1.1, .inr (.inr (.inl pending))))
    | .inr point => core.postFn routines (value.1.1, caller.advance (pending.2,
        .inr (routines.fmaFn (routines.corrFn (value.1.1.1, pending.1.1), (pending.1.2, point)))))
  | .inr (.inr (.inr forged)) => .inl (finishFn (forged, value.1.1))

/-- The wrapper's step. -/
def advanceImpl (callerReserve : caller.continuation.code.memBound + 50 < 2 ^ w) :
    Implementation .unit core.advanceInput (core.output out outLe) (core.advanceFn (finishFn := finishFn) routines caller) :=
  ((core.reorderAdvance.then
    (Implementation.distribute core.stateAll core.tail₁ core.tailRest core.wordFits
      (core.fitsSum3 (core.le3 core.stateAll_le) (core.le3 core.tail₁_le) (by have := core.tailRest_le; omega)))).then
    (Implementation.branch (core.readyStep routines caller out outLe callerReserve)
      (core.tail₁React routines caller out outLe finish callerReserve) (by decide) core.wordFits
      (core.fitsSum core.readyInput_le core.tail₁Input_le))).castFunction (by
      funext value
      rcases value with ⟨⟨keyed, state | pending | pending | forged⟩, coins | point⟩ <;> rfl)

/-! ### Initialization -/
abbrev keyAll' := Layout.all core.key.representation
theorem keyAll'_le : core.keyAll'.representation.encoding.words ≤ core.bound := by
  rw [Layout.all_words]
  change core.inner.key.representation.encoding.words + core.scalar.representation.encoding.words ≤ _
  unfold bound width
  omega
/-- The empty slot list. -/
def emptySlots : Implementation .unit core.keyAll' core.slots (fun _ => []) :=
  Implementation.constant core.keyAll' core.slots ⟨[], ⟨by simp, by simp⟩⟩ core.wordFits
/-- The wrapper's first step, as a function. -/
def initialFn (value : core.key.Value) :
    (M × (scalar.Value base × (List (scalar.Value base) × List (scalar.Value base)))) ⊕
      (core.inner.good.Request × ((core.scalar.Value × List (Unit ⊕ scalar.Value base)) ×
        (A ⊕ ((core.message.Value × A) ⊕ (((core.message.Value × core.point.Value) × A) ⊕ core.forgeryIn.Value))))) :=
  core.postFn routines ((⟨value.val.2, value.property.2⟩, []), caller.initial ⟨value.val.1, value.property.1⟩)
/-- The wrapper's first step. -/
def initialImpl (initialReserve : caller.initialCode.code.memBound + 50 < 2 ^ w) :
    Implementation .unit core.keyAll' (core.output out outLe) (core.initialFn routines caller) :=
  ((((Implementation.allSecond core.inner.key core.scalar core.wordFits _).pair' core.emptySlots core.wordFits
      (Implementation.allSecond_buffers _ _ _ _) (Implementation.constant_buffers _ _ _ _) (core.room (by omega))
      (core.fits4' (core.le3 core.keyAll'_le) (core.le3 core.scalarAll_le) (core.le3 core.slots_le))).pair'
    ((Implementation.allFirst core.inner.key core.scalar core.wordFits _).then (core.innerInitial caller)) core.wordFits
    (Implementation.pair'_buffers _ _ _ _ _ _ _)
    (Implementation.then_buffers _ _ (Implementation.allFirst_buffers _ _ _ _) (core.innerInitial_buffers caller))
    (by have := initialReserve; omega)
    (core.fits4' (core.le3 core.keyAll'_le) (core.le3 core.keyed_le) (core.le3 core.nextSplit_le))).then
    (core.post routines out outLe)).castFunction rfl

end Core
end Finish

end Signatures.Runtime.CaliperBackend.SyncWrap
