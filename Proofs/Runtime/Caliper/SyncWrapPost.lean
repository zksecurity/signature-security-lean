import Proofs.Runtime.Caliper.SyncWrapRequests

/-! One inner step and the wrapper's reaction to it. `innerStep` runs the inner caller's
continuation and splits its answer; `post` turns a returned forgery into the final hash
request and a pending inner request into the forwarded request, recording the hash slot and,
before a signing query, the correction. -/
namespace Signatures.Runtime.CaliperBackend.SyncWrap
open Caliper BoundedSource WeightedFull

variable {w : Nat} {K M G F PK A : Type} [Zero F] (core : Core w K M G F PK A)

/-- The wrapper's local routines, with their buffer reservations. -/
structure Routines (core : Core w K M G F PK A) where
  hashOfFn : core.message.Value → core.keyLayout.Value
  hashOf : Implementation .unit core.messageAll core.keyAll hashOfFn
  corrFn : core.scalar.Value × core.message.Value → core.scalar.Value
  corr : Implementation .unit (core.scalarAll.prod core.messageAll
    (core.fits (by rw [Layout.all_words, Layout.all_words]; unfold Core.width; omega))) core.scalarAll corrFn
  fmaFn : core.scalar.Value × (core.point.Value × core.point.Value) → core.point.Value
  fma : Implementation .unit (core.scalarAll.prod (core.pointAll.prod core.pointAll
      (core.fits (by rw [Layout.all_words]; unfold Core.width; omega)))
    (core.fits (by rw [Layout.all_words, Layout.prod_words, Layout.all_words]; unfold Core.width; omega))) core.pointAll fmaFn
  slots : Nat
  reserve : slots + 50 < 2 ^ w
  hashOfBuffers : hashOf.program.code.memBound ≤ slots
  corrBuffers : corr.program.code.memBound ≤ slots
  fmaBuffers : fma.program.code.memBound ≤ slots
  /-- One time and one stored-code budget covering each routine. -/
  time : Nat
  words : Nat
  hashOfBound : hashOf.BoundedBy time words
  corrBound : corr.BoundedBy time words
  fmaBound : fma.BoundedBy time words
  hashOfNames : NamesAccounted hashOf.program.code slots
  corrNames : NamesAccounted corr.program.code slots
  fmaNames : NamesAccounted fma.program.code slots

namespace Core

theorem requestAll_words : core.requestAll.representation.encoding.words = core.requestRep.encoding.words := rfl
theorem replyAll_words : core.replyAll.representation.encoding.words = core.replyRep.encoding.words := rfl

/-! ## Layouts of the inner step's answer and the wrapper's output -/
theorem pendingFits : core.requestAll.representation.encoding.words + core.stateAll.representation.encoding.words < 2 ^ w := by
  have := core.requestAll_words; have := core.stateAll_words; exact core.fits (by unfold width; omega)
abbrev pendingAll : Layout w (core.inner.good.Request × A) := core.requestAll.prod core.stateAll core.pendingFits
theorem pendingAll_words : core.pendingAll.representation.encoding.words = core.requestRep.encoding.words + core.inner.state.encoding.words := rfl
theorem nextFits : 1 + max core.forgeryAll.representation.encoding.words core.pendingAll.representation.encoding.words < 2 ^ w := by
  have := core.forgeryAll_words; have := core.pendingAll_words; exact core.fits (by unfold width; omega)
/-- The inner caller's answer: a forgery, or a request with the next inner state. -/
abbrev nextSplit : Layout w (core.forgeryIn.Value ⊕ (core.inner.good.Request × A)) :=
  core.forgeryAll.sum core.pendingAll (width_pos core.wordFits) core.nextFits
theorem nextSplit_words : core.nextSplit.representation.encoding.words ≤ 1 + core.width := by
  have := core.forgeryAll_words; have := core.pendingAll_words
  change 1 + max _ _ ≤ _; unfold width; omega
theorem pendingWrapperFits : core.requestAll.representation.encoding.words + core.wrapper.representation.encoding.words < 2 ^ w := by
  have := core.wrapper_words; have := core.requestAll_words; exact core.fits (by unfold width at *; omega)
/-- A forwarded request with the wrapper's next state. -/
abbrev pendingWrapper := core.requestAll.prod core.wrapper core.pendingWrapperFits

theorem resumeFits : core.inner.state.encoding.words + core.replyRep.encoding.words < 2 ^ w := core.fits (by unfold width; omega)

end Core

/-! ## The inner step -/
section Step
variable {Atom : Type} {base : Atom → Type} {key scalar : Ty Atom} {M G PK A : Type} [Zero (scalar.Value base)]
  (core : Core w (key.Value base) M G (scalar.Value base) PK A) (caller : SharedCaller core.inner)

namespace Core
/-- Split the inner caller's answer packet. -/
def splitNext : Implementation .unit (Layout.all (CallerStep.next core.inner.good.control)) core.nextSplit id :=
  ((Implementation.allSum (a := core.forgeryIn.representation) (b := CallerStep.pending core.inner.good.control) core.wordFits
      (CallerStep.next core.inner.good.control).fits).then
    (Implementation.branch (Implementation.inl core.forgeryAll core.pendingAll core.wordFits core.nextFits)
      ((Implementation.allProd (a := core.requestRep) (b := core.inner.state) core.wordFits core.pendingFits).then
        (Implementation.inr core.forgeryAll core.pendingAll core.wordFits core.nextFits)) (by decide) core.wordFits
      (CallerStep.next core.inner.good.control).fits)).castFunction (by
      funext value
      cases value <;> rfl)
theorem splitNext_buffers : core.splitNext.program.code.memBound ≤ 3 :=
  (Implementation.castFunction_buffers _ _ (Implementation.then_buffers _ _ (Implementation.view_buffers _ _ _)
    (Implementation.branch_buffers _ _ _ _ (Implementation.inl_buffers _ _ _ _)
      (Implementation.then_buffers _ _ (Implementation.view_buffers _ _ _) (Implementation.inr_buffers _ _ _ _))))).trans (by omega)

/-- Run the inner caller's continuation and split its answer. -/
def innerStep : Implementation .unit (core.stateAll.prod core.replyAll core.resumeFits) core.nextSplit caller.advance :=
  (((Implementation.allProd' (a := core.inner.state) (b := core.replyRep) core.wordFits core.resumeFits).then
    (Implementation.ofRealizer caller.continuation)).then core.splitNext).castFunction (by funext value; rfl)
/-- Run the inner caller's initialization and split its answer. -/
def innerInitial : Implementation .unit (Layout.all core.inner.key.representation) core.nextSplit caller.initial :=
  ((Implementation.ofRealizer caller.initialCode).then core.splitNext).castFunction (by funext value; rfl)
theorem innerInitial_buffers : (core.innerInitial caller).program.code.memBound ≤ max caller.initialCode.code.memBound 3 :=
  (Implementation.castFunction_buffers _ _ (Implementation.then_buffers _ _ (Implementation.ofRealizer_buffers _ le_rfl)
    core.splitNext_buffers)).trans (by omega)
end Core

end Step

/-! ## Word bounds, all against one width -/
namespace Core
variable (core : Core w K M G F PK A)

def bound : Nat := 5 + 3 * core.width
theorem width_pos' : 4 ≤ core.width := by unfold width; omega
theorem scalarAll_le : core.scalarAll.representation.encoding.words ≤ core.bound := by rw [scalarAll_words]; unfold bound width; omega
theorem messageAll_le : core.messageAll.representation.encoding.words ≤ core.bound := by rw [messageAll_words]; unfold bound width; omega
theorem pointAll_le : core.pointAll.representation.encoding.words ≤ core.bound := by rw [pointAll_words]; unfold bound width; omega
theorem forgeryAll_le : core.forgeryAll.representation.encoding.words ≤ core.bound := by rw [forgeryAll_words]; unfold bound width; omega
theorem stateAll_le : core.stateAll.representation.encoding.words ≤ core.bound := by rw [stateAll_words]; unfold bound width; omega
theorem requestAll_le : core.requestAll.representation.encoding.words ≤ core.bound := by rw [requestAll_words]; unfold bound width; omega
theorem replyAll_le : core.replyAll.representation.encoding.words ≤ core.bound := by rw [replyAll_words]; unfold bound width; omega
theorem groupAll_le : core.groupAll.representation.encoding.words ≤ core.bound := by
  rw [groupAll_words]; have := core.requestRep_words; unfold bound width; omega
theorem uniformAll_le : core.uniformAll.representation.encoding.words ≤ core.bound := by
  rw [uniformAll_words]; have := core.requestRep_words; unfold bound width; omega
theorem keyAll_le : core.keyAll.representation.encoding.words ≤ core.bound := by
  rw [keyAll_words]; have := core.requestRep_words; have := core.groupRep_words; unfold bound width; omega
theorem uniformReplyAll_le : core.uniformReplyAll.representation.encoding.words ≤ core.bound := by
  rw [uniformReplyAll_words]; have := core.replyRep_words; unfold bound width; omega
theorem slots_le : core.slots.representation.encoding.words ≤ core.bound := by rw [slots_words]; unfold bound width; omega
theorem slotEntry_le : core.slotEntry.representation.encoding.words ≤ core.bound := by rw [slotEntry_words]; unfold bound width; omega
theorem keyed_le : core.keyed.representation.encoding.words ≤ core.bound := by rw [keyed_words]; unfold bound width; omega
theorem preSign_le : core.preSign.representation.encoding.words ≤ core.bound := by
  have := core.messageAll_words; have := core.stateAll_words; change _ + _ ≤ _; unfold bound width; omega
theorem afterHash_le : core.afterHash.representation.encoding.words ≤ core.bound := by
  have := core.messageAll_words; have := core.stateAll_words; have := core.pointAll_words; change (_ + _) + _ ≤ _; unfold bound width; omega
theorem tail₂_le : core.tail₂.representation.encoding.words ≤ core.bound := by have := core.tail₂_words; unfold bound width at *; omega
theorem tail₁_le : core.tail₁.representation.encoding.words ≤ core.bound := by have := core.tail₁_words; unfold bound width at *; omega
theorem mode_le : core.mode.representation.encoding.words ≤ core.bound := by have := core.mode_words; unfold bound width at *; omega
theorem wrapper_le : core.wrapper.representation.encoding.words ≤ core.bound := by have := core.wrapper_words; unfold bound width at *; omega
theorem pendingAll_le : core.pendingAll.representation.encoding.words ≤ core.bound := by
  rw [pendingAll_words]; unfold bound width; omega
theorem nextSplit_le : core.nextSplit.representation.encoding.words ≤ core.bound := by have := core.nextSplit_words; unfold bound width at *; omega
theorem pendingWrapper_le : core.pendingWrapper.representation.encoding.words ≤ core.bound := by
  have := core.wrapper_words; rw [Layout.prod_words, requestAll_words]; unfold bound width at *; omega

theorem _root_.Signatures.Runtime.CaliperBackend.BoundedSource.Layout.prod_le {X Y : Type} (left : Layout w X) (right : Layout w Y) (fits) {a b : Nat}
    (ha : left.representation.encoding.words ≤ a) (hb : right.representation.encoding.words ≤ b) :
    (left.prod right fits).representation.encoding.words ≤ a + b := by rw [Layout.prod_words]; omega
/-- Four layout widths within three bounds fit a word. -/
theorem fits4 {a b c d : Nat} (ha : a ≤ 3 * core.bound) (hb : b ≤ 3 * core.bound) (hc : c ≤ 3 * core.bound) (hd : d ≤ 3 * core.bound) :
    a + b + c + d < 2 ^ w := core.fits (by have := core.width_pos'; simp only [bound] at *; omega)
theorem fits2 {a b : Nat} (ha : a ≤ 3 * core.bound) (hb : b ≤ 3 * core.bound) : a + b < 2 ^ w :=
  core.fits (by have := core.width_pos'; simp only [bound] at *; omega)
theorem fitsSum {a b : Nat} (ha : a ≤ 3 * core.bound) (hb : b ≤ 3 * core.bound) : 1 + max a b < 2 ^ w :=
  core.fits (by have := core.width_pos'; simp only [bound] at *; omega)
theorem fitsSum3 {a b c : Nat} (ha : a ≤ 3 * core.bound) (hb : b ≤ 3 * core.bound) (hc : c ≤ 3 * core.bound) : 1 + max a b + c < 2 ^ w :=
  core.fits (by have := core.width_pos'; simp only [bound] at *; omega)
theorem le3 {a : Nat} (ha : a ≤ core.bound) : a ≤ 3 * core.bound := by omega
include core in
/-- Small buffer counts fit a word. -/
theorem room {n : Nat} (small : n ≤ 100) : n + 2 < 2 ^ w := core.fits (by have := core.width_pos'; omega)
end Core

/-! ## Reacting to the inner caller's answer -/
section Final
variable {Atom : Type} {base : Atom → Type} {key scalar : Ty Atom} {M G PK A : Type} [Zero (scalar.Value base)]
  (core : Core w (key.Value base) M G (scalar.Value base) PK A) (routines : Routines core)

namespace Core

/-- The forgery's message, read from a certified forgery. -/
def forgeryMessage : Implementation .unit core.forgeryAll core.messageAll (fun value => ⟨value.val.1, value.property.1⟩) :=
  Implementation.allFirst core.message core.inner.good.extraction.forgeryTail core.wordFits core.forgeryIn.representation.fits
theorem forgeryMessage_buffers : core.forgeryMessage.program.code.memBound ≤ 2 := Implementation.allFirst_buffers _ _ _ _

/-- A returned inner forgery beside the key and slots. -/
abbrev finalInput := core.forgeryAll.prod core.keyed (core.fits2 (core.le3 core.forgeryAll_le) (core.le3 core.keyed_le))
theorem finalInput_le : core.finalInput.representation.encoding.words ≤ 2 * core.bound :=
  (Layout.prod_le _ _ _ core.forgeryAll_le core.keyed_le).trans (by omega)
theorem finalInput_fits4 {c d : Nat} (hc : c ≤ 3 * core.bound) (hd : d ≤ 3 * core.bound) :
    core.finalInput.representation.encoding.words + core.finalInput.representation.encoding.words + c + d < 2 ^ w :=
  core.fits4 (by have := core.finalInput_le; omega) (by have := core.finalInput_le; omega) hc hd

/-- The final hash request. -/
def finalRequest : Implementation .unit core.finalInput core.requestAll
    (fun value => core.hashRequest (routines.hashOfFn ⟨value.1.val.1, value.1.property.1⟩)) :=
  ((((Implementation.first (by decide) core.forgeryAll core.keyed core.wordFits _).then core.forgeryMessage).then routines.hashOf).then
    core.hashRequestImpl).castFunction rfl
theorem finalRequest_buffers : (core.finalRequest routines).program.code.memBound ≤ max routines.slots 3 :=
  (Implementation.then_buffers _ _ (Implementation.then_buffers _ _ (Implementation.then_buffers _ _
    (Implementation.first_buffers _ _ _ _ _) core.forgeryMessage_buffers) routines.hashOfBuffers) core.hashRequestImpl_buffers).trans (by omega)
/-- The wrapper's state after the inner caller returned. -/
def finalState : Implementation .unit core.finalInput core.wrapper (fun value => (value.2, .inr (.inr (.inr value.1)))) :=
  ((Implementation.second (by decide) core.forgeryAll core.keyed core.wordFits _).pair'
    ((Implementation.first (by decide) core.forgeryAll core.keyed core.wordFits _).then core.modeFinal) core.wordFits
    (Implementation.second_buffers _ _ _ _ _) (Implementation.then_buffers _ _ (Implementation.first_buffers _ _ _ _ _) core.modeFinal_buffers)
    (core.room (by omega)) (core.finalInput_fits4 (core.le3 core.keyed_le) (core.le3 core.mode_le))).castFunction rfl
theorem finalState_buffers : core.finalState.program.code.memBound ≤ 4 :=
  (Implementation.castFunction_buffers _ _ (Implementation.pair'_buffers _ _ _ _ _ _ _)).trans (by omega)

end Core
end Final

section Output
variable {Atom : Type} {base : Atom → Type} {key scalar : Ty Atom} {M G PK A : Type} [Zero (scalar.Value base)]
  (core : Core w (key.Value base) M G (scalar.Value base) PK A) (routines : Routines core)
  (out : Layout w (M × (scalar.Value base × (List (scalar.Value base) × List (scalar.Value base)))))
  (outLe : out.representation.encoding.words ≤ core.outWords)

namespace Core

include outLe in
theorem out_le : out.representation.encoding.words ≤ core.bound := by unfold bound width; omega
include outLe in
theorem outputFits : 1 + max out.representation.encoding.words core.pendingWrapper.representation.encoding.words < 2 ^ w :=
  core.fitsSum (core.le3 (core.out_le out outLe)) (core.le3 core.pendingWrapper_le)
/-- The wrapper's answer: a wrapped forgery, or a request with the wrapper's next state. -/
abbrev output := out.sum core.pendingWrapper (width_pos core.wordFits) (core.outputFits out outLe)

/-- Hash the forgery's period and remember the forgery. -/
def finalReact : Implementation .unit core.finalInput (core.output out outLe)
    (fun value => .inr (core.hashRequest (routines.hashOfFn ⟨value.1.val.1, value.1.property.1⟩), (value.2, .inr (.inr (.inr value.1))))) :=
  (((core.finalRequest routines).pair' core.finalState core.wordFits (core.finalRequest_buffers routines) core.finalState_buffers
    (by have := routines.reserve; omega)
    (core.finalInput_fits4 (core.le3 core.requestAll_le) (core.le3 core.wrapper_le))).then
    (Implementation.inr out core.pendingWrapper core.wordFits (core.outputFits out outLe))).castFunction rfl

end Core
end Output

/-! ## Forwarding an inner request -/
section Pending
variable {Atom : Type} {base : Atom → Type} {key scalar : Ty Atom} {M G PK A : Type} [Zero (scalar.Value base)]
  (core : Core w (key.Value base) M G (scalar.Value base) PK A) (routines : Routines core)

namespace Core

/-- The inner state beside the key and slots. -/
abbrev rest := core.stateAll.prod core.keyed (core.fits2 (core.le3 core.stateAll_le) (core.le3 core.keyed_le))
theorem rest_le : core.rest.representation.encoding.words ≤ 2 * core.bound :=
  (Layout.prod_le _ _ _ core.stateAll_le core.keyed_le).trans (by omega)
/-- A pending inner request beside the key and slots. -/
abbrev pendingInput := core.pendingAll.prod core.keyed (core.fits2 (core.le3 core.pendingAll_le) (core.le3 core.keyed_le))
theorem pendingInput_le : core.pendingInput.representation.encoding.words ≤ 2 * core.bound :=
  (Layout.prod_le _ _ _ core.pendingAll_le core.keyed_le).trans (by omega)
theorem rest_fits4 {a c d : Nat} (ha : a ≤ 3 * core.bound) (hc : c ≤ 3 * core.bound) (hd : d ≤ 3 * core.bound) :
    (core.rest.representation.encoding.words + a) + (core.rest.representation.encoding.words + a) + c + d < 2 ^ w :=
  core.fits (by have := core.rest_le; have := core.width_pos'; simp only [bound] at *; omega)

/-- Move the request in front of the state and the key. -/
def reorderPending : Implementation .unit core.pendingInput (core.requestAll.prod core.rest (core.fits2 (core.le3 core.requestAll_le) (by have := core.rest_le; omega)))
    (fun value => (value.1.1, (value.1.2, value.2))) :=
  (((Implementation.first (by decide) core.pendingAll core.keyed core.wordFits _).then
      (Implementation.first (by decide) core.requestAll core.stateAll core.wordFits _)).pair'
    (((Implementation.first (by decide) core.pendingAll core.keyed core.wordFits _).then
      (Implementation.second (by decide) core.requestAll core.stateAll core.wordFits _)).pair'
      (Implementation.second (by decide) core.pendingAll core.keyed core.wordFits _) core.wordFits
      (Implementation.then_buffers _ _ (Implementation.first_buffers _ _ _ _ _) (Implementation.second_buffers _ _ _ _ _))
      (Implementation.second_buffers _ _ _ _ _) (core.room (by omega))
      (core.fits4 (by rw [Layout.prod_words]; have := core.pendingAll_le; have := core.keyed_le; omega)
        (by rw [Layout.prod_words]; have := core.pendingAll_le; have := core.keyed_le; omega) (core.le3 core.stateAll_le)
        (core.le3 core.keyed_le)))
    core.wordFits (Implementation.then_buffers _ _ (Implementation.first_buffers _ _ _ _ _) (Implementation.first_buffers _ _ _ _ _))
    (Implementation.pair'_buffers _ _ _ _ _ _ _) (core.room (by omega))
    (core.fits4 (by rw [Layout.prod_words]; have := core.pendingAll_le; have := core.keyed_le; omega)
      (by rw [Layout.prod_words]; have := core.pendingAll_le; have := core.keyed_le; omega) (core.le3 core.requestAll_le)
      (by rw [Layout.prod_words]; have := core.stateAll_le; have := core.keyed_le; omega))).castFunction rfl
theorem reorderPending_buffers : core.reorderPending.program.code.memBound ≤ 6 := by
  unfold reorderPending
  exact (Implementation.castFunction_buffers _ _ (Implementation.pair'_buffers _ _ _ _ _ _ _)).trans (by omega)

/-! ### The three request kinds -/
abbrev randomInput := core.uniformAll.prod core.rest (core.fits2 (core.le3 core.uniformAll_le) (by have := core.rest_le; omega))
abbrev groupInput := core.groupAll.prod core.rest (core.fits2 (core.le3 core.groupAll_le) (by have := core.rest_le; omega))
abbrev hashInput := core.keyAll.prod core.rest (core.fits2 (core.le3 core.keyAll_le) (by have := core.rest_le; omega))
abbrev signInput := core.messageAll.prod core.rest (core.fits2 (core.le3 core.messageAll_le) (by have := core.rest_le; omega))
theorem randomInput_le : core.randomInput.representation.encoding.words ≤ 3 * core.bound :=
  (Layout.prod_le _ _ _ core.uniformAll_le core.rest_le).trans (by omega)
theorem groupInput_le : core.groupInput.representation.encoding.words ≤ 3 * core.bound :=
  (Layout.prod_le _ _ _ core.groupAll_le core.rest_le).trans (by omega)
theorem hashInput_le : core.hashInput.representation.encoding.words ≤ 3 * core.bound :=
  (Layout.prod_le _ _ _ core.keyAll_le core.rest_le).trans (by omega)
theorem signInput_le : core.signInput.representation.encoding.words ≤ 3 * core.bound :=
  (Layout.prod_le _ _ _ core.messageAll_le core.rest_le).trans (by omega)
theorem fits4' {a c d : Nat} (ha : a ≤ 3 * core.bound) (hc : c ≤ 3 * core.bound) (hd : d ≤ 3 * core.bound) :
    a + a + c + d < 2 ^ w := core.fits (by have := core.width_pos'; simp only [bound] at *; omega)

/-- Forward a request for coins: the inner state becomes the ready mode. -/
def randomState : Implementation .unit core.randomInput core.wrapper (fun value => (value.2.2, .inl value.2.1)) :=
  (((Implementation.second (by decide) core.uniformAll core.rest core.wordFits _).then
      (Implementation.second (by decide) core.stateAll core.keyed core.wordFits _)).pair'
    (((Implementation.second (by decide) core.uniformAll core.rest core.wordFits _).then
      (Implementation.first (by decide) core.stateAll core.keyed core.wordFits _)).then core.modeReady) core.wordFits
    (Implementation.then_buffers _ _ (Implementation.second_buffers _ _ _ _ _) (Implementation.second_buffers _ _ _ _ _))
    (Implementation.then_buffers _ _ (Implementation.then_buffers _ _ (Implementation.second_buffers _ _ _ _ _)
      (Implementation.first_buffers _ _ _ _ _)) core.modeReady_buffers)
    (core.room (by omega)) (core.fits4' core.randomInput_le (core.le3 core.keyed_le) (core.le3 core.mode_le))).castFunction rfl
theorem randomState_buffers : core.randomState.program.code.memBound ≤ 4 :=
  (Implementation.castFunction_buffers _ _ (Implementation.pair'_buffers _ _ _ _ _ _ _)).trans (by omega)
def randomRequestPart : Implementation .unit core.randomInput core.requestAll (fun value => core.randomRequest value.1) :=
  ((Implementation.first (by decide) core.uniformAll core.rest core.wordFits _).then core.randomRequestImpl).castFunction rfl
theorem randomRequestPart_buffers : core.randomRequestPart.program.code.memBound ≤ 3 :=
  (Implementation.then_buffers _ _ (Implementation.first_buffers _ _ _ _ _) core.randomRequestImpl_buffers).trans (by omega)

/-- Forward a hash request: remember the attacker's own slot. -/
def hashState : Implementation .unit core.hashInput core.wrapper
    (fun value => ((value.2.2.1, core.append (own (scalar.Value base), value.2.2.2)), .inl value.2.1)) :=
  ((((Implementation.second (by decide) core.keyAll core.rest core.wordFits _).then
      (Implementation.second (by decide) core.stateAll core.keyed core.wordFits _)).then core.appendOwn).pair'
    (((Implementation.second (by decide) core.keyAll core.rest core.wordFits _).then
      (Implementation.first (by decide) core.stateAll core.keyed core.wordFits _)).then core.modeReady) core.wordFits
    (Implementation.then_buffers _ _ (Implementation.then_buffers _ _ (Implementation.second_buffers _ _ _ _ _)
      (Implementation.second_buffers _ _ _ _ _)) core.appendOwn_buffers)
    (Implementation.then_buffers _ _ (Implementation.then_buffers _ _ (Implementation.second_buffers _ _ _ _ _)
      (Implementation.first_buffers _ _ _ _ _)) core.modeReady_buffers)
    (core.room (by omega)) (core.fits4' core.hashInput_le (core.le3 core.keyed_le) (core.le3 core.mode_le))).castFunction rfl
theorem hashState_buffers : core.hashState.program.code.memBound ≤ 42 :=
  (Implementation.castFunction_buffers _ _ (Implementation.pair'_buffers _ _ _ _ _ _ _)).trans (by omega)
def hashRequestPart : Implementation .unit core.hashInput core.requestAll (fun value => core.hashRequest value.1) :=
  ((Implementation.first (by decide) core.keyAll core.rest core.wordFits _).then core.hashRequestImpl).castFunction rfl
theorem hashRequestPart_buffers : core.hashRequestPart.program.code.memBound ≤ 3 :=
  (Implementation.then_buffers _ _ (Implementation.first_buffers _ _ _ _ _) core.hashRequestImpl_buffers).trans (by omega)

/-- Before a signing query: hash the message's period, remember the corrected slot. -/
def signRequestPart : Implementation .unit core.signInput core.requestAll (fun value => core.hashRequest (routines.hashOfFn value.1)) :=
  (((Implementation.first (by decide) core.messageAll core.rest core.wordFits _).then routines.hashOf).then core.hashRequestImpl).castFunction rfl
theorem signRequestPart_buffers : (core.signRequestPart routines).program.code.memBound ≤ max routines.slots 3 :=
  (Implementation.then_buffers _ _ (Implementation.then_buffers _ _ (Implementation.first_buffers _ _ _ _ _) routines.hashOfBuffers)
    core.hashRequestImpl_buffers).trans (by omega)
/-- The known key, from a pending signing input. -/
def signKey : Implementation .unit core.signInput core.scalarAll (fun value => value.2.2.1) :=
  ((Implementation.second (by decide) core.messageAll core.rest core.wordFits _).then
    (Implementation.second (by decide) core.stateAll core.keyed core.wordFits _)).then
    (Implementation.first (by decide) core.scalarAll core.slots core.wordFits _)
theorem signKey_buffers : core.signKey.program.code.memBound ≤ 2 :=
  (Implementation.then_buffers _ _ (Implementation.then_buffers _ _ (Implementation.second_buffers _ _ _ _ _) (Implementation.second_buffers _ _ _ _ _))
    (Implementation.first_buffers _ _ _ _ _)).trans (by omega)
def signSlots : Implementation .unit core.signInput core.slots (fun value => value.2.2.2) :=
  ((Implementation.second (by decide) core.messageAll core.rest core.wordFits _).then
    (Implementation.second (by decide) core.stateAll core.keyed core.wordFits _)).then
    (Implementation.second (by decide) core.scalarAll core.slots core.wordFits _)
theorem signSlots_buffers : core.signSlots.program.code.memBound ≤ 2 :=
  (Implementation.then_buffers _ _ (Implementation.then_buffers _ _ (Implementation.second_buffers _ _ _ _ _) (Implementation.second_buffers _ _ _ _ _))
    (Implementation.second_buffers _ _ _ _ _)).trans (by omega)
theorem entryFits : 1 + max (DataImplementation.unitLayout w).representation.encoding.words core.scalar.representation.encoding.words < 2 ^ w :=
  core.slotEntry.representation.fits
/-- The corrected slot for a signing query. -/
def signEntry : Implementation .unit core.signInput core.slotEntry (fun value => .inr (routines.corrFn (value.2.2.1, value.1)).val) :=
  ((((core.signKey.pair' (Implementation.first (by decide) core.messageAll core.rest core.wordFits _) core.wordFits core.signKey_buffers
      (Implementation.first_buffers _ _ _ _ _) (core.room (by omega))
      (core.fits4' core.signInput_le (core.le3 core.scalarAll_le) (core.le3 core.messageAll_le))).then routines.corr).then
    (Implementation.unall (width_pos core.wordFits) core.scalar)).then
    (Implementation.inr (DataImplementation.unitLayout w) core.scalar core.wordFits core.entryFits)).castFunction rfl
theorem signEntry_buffers : (core.signEntry routines).program.code.memBound ≤ max routines.slots 3 :=
  (Implementation.castFunction_buffers _ _ (Implementation.then_buffers _ _ (Implementation.then_buffers _ _ (Implementation.then_buffers _ _
    (Implementation.pair'_buffers _ _ _ _ _ _ _) routines.corrBuffers) (Implementation.recast_buffers _ _ _ _ _ _))
    (Implementation.inr_buffers _ _ _ _))).trans (by omega)
/-- The key and the slots after a signing query was announced. -/
def signKeyed : Implementation .unit core.signInput core.keyed
    (fun value => (value.2.2.1, core.append (.inr (routines.corrFn (value.2.2.1, value.1)).val, value.2.2.2))) :=
  (core.signKey.pair' (((core.signEntry routines).pair' core.signSlots core.wordFits (core.signEntry_buffers routines) core.signSlots_buffers
      (by have := routines.reserve; omega) (core.fits4' core.signInput_le (core.le3 core.slotEntry_le) (core.le3 core.slots_le))).then core.snoc)
    core.wordFits core.signKey_buffers
    (Implementation.then_buffers _ _ (Implementation.pair'_buffers _ _ _ _ _ _ _) core.snoc_buffers) (by have := routines.reserve; omega)
    (core.fits4' core.signInput_le (core.le3 core.scalarAll_le) (core.le3 core.slots_le))).castFunction rfl
theorem signKeyed_buffers : (core.signKeyed routines).program.code.memBound ≤ max routines.slots 40 + 2 :=
  (Implementation.castFunction_buffers _ _ (Implementation.pair'_buffers _ _ _ _ _ _ _)).trans (by omega)
def signMode : Implementation .unit core.signInput core.mode (fun value => .inr (.inl (value.1, value.2.1))) :=
  (((Implementation.first (by decide) core.messageAll core.rest core.wordFits _).pair'
    ((Implementation.second (by decide) core.messageAll core.rest core.wordFits _).then
      (Implementation.first (by decide) core.stateAll core.keyed core.wordFits _)) core.wordFits (Implementation.first_buffers _ _ _ _ _)
    (Implementation.then_buffers _ _ (Implementation.second_buffers _ _ _ _ _) (Implementation.first_buffers _ _ _ _ _)) (core.room (by omega))
    (core.fits4' core.signInput_le (core.le3 core.messageAll_le) (core.le3 core.stateAll_le))).then core.modePreSign).castFunction rfl
theorem signMode_buffers : core.signMode.program.code.memBound ≤ 3 :=
  (Implementation.castFunction_buffers _ _ (Implementation.then_buffers _ _ (Implementation.pair'_buffers _ _ _ _ _ _ _) core.modePreSign_buffers)).trans
    (by omega)
def signState : Implementation .unit core.signInput core.wrapper
    (fun value => ((value.2.2.1, core.append (.inr (routines.corrFn (value.2.2.1, value.1)).val, value.2.2.2)), .inr (.inl (value.1, value.2.1)))) :=
  ((core.signKeyed routines).pair' core.signMode core.wordFits (core.signKeyed_buffers routines) core.signMode_buffers
    (by have := routines.reserve; omega) (core.fits4' core.signInput_le (core.le3 core.keyed_le) (core.le3 core.mode_le))).castFunction rfl
theorem signState_buffers : (core.signState routines).program.code.memBound ≤ max routines.slots 40 + 3 :=
  (Implementation.castFunction_buffers _ _ (Implementation.pair'_buffers _ _ _ _ _ _ _)).trans (by omega)

end Core
end Pending

/-! ## Assembling the reaction -/
section React
variable {Atom : Type} {base : Atom → Type} {key scalar : Ty Atom} {M G PK A : Type} [Zero (scalar.Value base)]
  (core : Core w (key.Value base) M G (scalar.Value base) PK A) (routines : Routines core)
  (out : Layout w (M × (scalar.Value base × (List (scalar.Value base) × List (scalar.Value base)))))
  (outLe : out.representation.encoding.words ≤ core.outWords)

namespace Core

def randomReact : Implementation .unit core.randomInput (core.output out outLe)
    (fun value => .inr (core.randomRequest value.1, (value.2.2, .inl value.2.1))) :=
  ((core.randomRequestPart.pair' core.randomState core.wordFits core.randomRequestPart_buffers core.randomState_buffers (core.room (by omega))
    (core.fits4' core.randomInput_le (core.le3 core.requestAll_le) (core.le3 core.wrapper_le))).then
    (Implementation.inr out core.pendingWrapper core.wordFits (core.outputFits out outLe))).castFunction rfl
def hashReact : Implementation .unit core.hashInput (core.output out outLe)
    (fun value => .inr (core.hashRequest value.1, ((value.2.2.1, core.append (own (scalar.Value base), value.2.2.2)), .inl value.2.1))) :=
  ((core.hashRequestPart.pair' core.hashState core.wordFits core.hashRequestPart_buffers core.hashState_buffers (core.room (by omega))
    (core.fits4' core.hashInput_le (core.le3 core.requestAll_le) (core.le3 core.wrapper_le))).then
    (Implementation.inr out core.pendingWrapper core.wordFits (core.outputFits out outLe))).castFunction rfl
def signReact : Implementation .unit core.signInput (core.output out outLe)
    (fun value => .inr (core.hashRequest (routines.hashOfFn value.1),
      ((value.2.2.1, core.append (.inr (routines.corrFn (value.2.2.1, value.1)).val, value.2.2.2)), .inr (.inl (value.1, value.2.1))))) :=
  (((core.signRequestPart routines).pair' (core.signState routines) core.wordFits (core.signRequestPart_buffers routines)
    (core.signState_buffers routines) (by have := routines.reserve; omega)
    (core.fits4' core.signInput_le (core.le3 core.requestAll_le) (core.le3 core.wrapper_le))).then
    (Implementation.inr out core.pendingWrapper core.wordFits (core.outputFits out outLe))).castFunction rfl

/-- Dispatch a hash or signing request. -/
def groupReact : Implementation .unit core.groupInput (core.output out outLe)
    (fun value => match value.1 with
      | .inl index => .inr (core.hashRequest index, ((value.2.2.1, core.append (own (scalar.Value base), value.2.2.2)), .inl value.2.1))
      | .inr message => .inr (core.hashRequest (routines.hashOfFn message),
          ((value.2.2.1, core.append (.inr (routines.corrFn (value.2.2.1, message)).val, value.2.2.2)), .inr (.inl (message, value.2.1))))) :=
  (((((Implementation.first (by decide) core.groupAll core.rest core.wordFits _).then
      (Implementation.allSum (a := core.keyLayout.representation) (b := core.message.representation) core.wordFits core.groupFits)).pair'
    (Implementation.second (by decide) core.groupAll core.rest core.wordFits _) core.wordFits
    (Implementation.then_buffers _ _ (Implementation.first_buffers _ _ _ _ _) (Implementation.view_buffers _ _ _))
    (Implementation.second_buffers _ _ _ _ _) (core.room (by omega))
    (core.fits4' core.groupInput_le (core.le3 (by
      rw [Layout.sum_words, Layout.all_words, Layout.all_words]; have := core.groupRep_words; have := core.requestRep_words
      unfold bound width; omega)) (by have := core.rest_le; omega))).then
    (Implementation.distribute core.keyAll core.messageAll core.rest core.wordFits
      (core.fitsSum3 (core.le3 core.keyAll_le) (core.le3 core.messageAll_le) (by have := core.rest_le; omega)))).then
    (Implementation.branch (core.hashReact out outLe) (core.signReact routines out outLe) (by decide) core.wordFits
      (core.fitsSum core.hashInput_le core.signInput_le))).castFunction (by
      funext value
      rcases value with ⟨index | message, rest⟩ <;> rfl)

/-- Forward a pending inner request. -/
def pendingReact : Implementation .unit core.pendingInput (core.output out outLe)
    (fun value => match value.1.1 with
      | .inl n => .inr (core.randomRequest n, (value.2, .inl value.1.2))
      | .inr (.inl index) => .inr (core.hashRequest index, ((value.2.1, core.append (own (scalar.Value base), value.2.2)), .inl value.1.2))
      | .inr (.inr message) => .inr (core.hashRequest (routines.hashOfFn message),
          ((value.2.1, core.append (.inr (routines.corrFn (value.2.1, message)).val, value.2.2)), .inr (.inl (message, value.1.2))))) :=
  ((core.reorderPending.then
    ((((Implementation.first (by decide) core.requestAll core.rest core.wordFits (core.fits2 (core.le3 core.requestAll_le) (by have := core.rest_le; omega))).then
      (Implementation.allSum (a := core.uniformRep) (b := core.groupRep) core.wordFits core.requestFits)).pair'
      (Implementation.second (by decide) core.requestAll core.rest core.wordFits (core.fits2 (core.le3 core.requestAll_le) (by have := core.rest_le; omega))) core.wordFits
      (Implementation.then_buffers _ _ (Implementation.first_buffers _ _ _ _ _) (Implementation.view_buffers _ _ _))
      (Implementation.second_buffers _ _ _ _ _) (core.room (by omega))
      (core.fits4' (by rw [Layout.prod_words]; have := core.requestAll_le; have := core.rest_le; omega)
        (core.le3 (by
          rw [Layout.sum_words, Layout.all_words, Layout.all_words]; have := core.requestRep_words
          unfold bound width; omega)) (by have := core.rest_le; omega))))).then
    ((Implementation.distribute core.uniformAll core.groupAll core.rest core.wordFits
      (core.fitsSum3 (core.le3 core.uniformAll_le) (core.le3 core.groupAll_le) (by have := core.rest_le; omega))).then
    (Implementation.branch (core.randomReact out outLe) (core.groupReact routines out outLe) (by decide) core.wordFits
      (core.fitsSum core.randomInput_le core.groupInput_le)))).castFunction (by
      funext value
      rcases value with ⟨⟨n | index | message, state⟩, keyed⟩ <;> rfl)

/-- The wrapper's reaction to the inner caller's answer, as a function. -/
def postFn (value : (core.scalar.Value × List (Unit ⊕ scalar.Value base)) × (core.forgeryIn.Value ⊕ (core.inner.good.Request × A))) :
    (M × (scalar.Value base × (List (scalar.Value base) × List (scalar.Value base)))) ⊕
      (core.inner.good.Request × ((core.scalar.Value × List (Unit ⊕ scalar.Value base)) ×
        (A ⊕ ((core.message.Value × A) ⊕ (((core.message.Value × core.point.Value) × A) ⊕ core.forgeryIn.Value))))) :=
  match value.2 with
  | .inl forged => .inr (core.hashRequest (routines.hashOfFn ⟨forged.val.1, forged.property.1⟩), (value.1, .inr (.inr (.inr forged))))
  | .inr (.inl n, state) => .inr (core.randomRequest n, (value.1, .inl state))
  | .inr (.inr (.inl index), state) =>
      .inr (core.hashRequest index, ((value.1.1, core.append (own (scalar.Value base), value.1.2)), .inl state))
  | .inr (.inr (.inr message), state) => .inr (core.hashRequest (routines.hashOfFn message),
      ((value.1.1, core.append (.inr (routines.corrFn (value.1.1, message)).val, value.1.2)), .inr (.inl (message, state))))

/-- React to the inner caller's answer. -/
def post : Implementation .unit (core.keyed.prod core.nextSplit (core.fits2 (core.le3 core.keyed_le) (core.le3 core.nextSplit_le)))
    (core.output out outLe) (core.postFn routines) :=
  (((Implementation.swap core.keyed core.nextSplit core.wordFits _).then
    (Implementation.distribute core.forgeryAll core.pendingAll core.keyed core.wordFits
      (core.fitsSum3 (core.le3 core.forgeryAll_le) (core.le3 core.pendingAll_le) (core.le3 core.keyed_le)))).then
    (Implementation.branch (core.finalReact routines out outLe) (core.pendingReact routines out outLe) (by decide) core.wordFits
      (core.fitsSum (by have := core.finalInput_le; omega) (by have := core.pendingInput_le; omega)))).castFunction (by
      funext value
      rcases value with ⟨keyed, forged | ⟨n | index | message, state⟩⟩ <;> rfl)

end Core
end React

end Signatures.Runtime.CaliperBackend.SyncWrap
