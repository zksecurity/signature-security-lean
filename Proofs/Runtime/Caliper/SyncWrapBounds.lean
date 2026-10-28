import Proofs.Runtime.Caliper.SyncWrapAdvance

/-! Time, stored-code and name budgets of the wrapper's step and initialization. Every piece is
bounded by a multiple of one unit: the layout bound plus the budgets of the local routines,
the slot append, the inner caller and the finishing code. -/
namespace Signatures.Runtime.CaliperBackend.SyncWrap
open Caliper BoundedSource WeightedFull

variable {w : Nat} {Atom : Type} {base : Atom → Type} {key scalar : Ty Atom} {M G PK A : Type} [Zero (scalar.Value base)]
  (core : Core w (key.Value base) M G (scalar.Value base) PK A) (routines : Routines core) (caller : SharedCaller core.inner)
  (innerBounds : Caller.Bounds core.inner.good core.inner.goodSetup caller)
  (out : Layout w (M × (scalar.Value base × (List (scalar.Value base) × List (scalar.Value base)))))
  (outLe : out.representation.encoding.words ≤ core.outWords)
  {finishFn : core.forgeryIn.Value × (core.scalar.Value × List (Unit ⊕ scalar.Value base)) →
    M × (scalar.Value base × (List (scalar.Value base) × List (scalar.Value base)))}
  (finish : Implementation .unit core.finalInput out finishFn)
  (finishTime finishWords finishSlots : Nat) (finishBound : finish.BoundedBy finishTime finishWords)
  (finishNames : NamesAccounted finish.program.code finishSlots)
  (callerReserve : caller.continuation.code.memBound + 50 < 2 ^ w)
  (initialReserve : caller.initialCode.code.memBound + 50 < 2 ^ w)


namespace Core

/-- One unit of time: the layout bound and every component budget. -/
def unitT : Nat := core.bound + routines.time + core.snocTime + innerBounds.step.time + innerBounds.initial.time + finishTime + 1
/-- One unit of stored code. -/
def unitW : Nat := core.bound + routines.words + core.snocWords + innerBounds.step.words + innerBounds.initial.words + finishWords + 1
/-- The name reservation covering every component. -/
def slotsAll : Nat := routines.slots + innerBounds.slots + finishSlots + 3

theorem width_eq : core.width = 4 + core.outWords + core.scalar.representation.encoding.words +
    (1 + core.slotCap * (1 + core.scalar.representation.encoding.words)) +
    core.inner.state.encoding.words + core.message.representation.encoding.words +
    core.point.representation.encoding.words + core.forgeryIn.representation.encoding.words +
    core.inner.key.representation.encoding.words + core.requestRep.encoding.words + core.replyRep.encoding.words := rfl

/-! ## Budgets of the reaction -/
local notation "T" => core.unitT routines caller innerBounds finishTime
local notation "W" => core.unitW routines caller innerBounds finishWords
local notation "S" => core.slotsAll routines caller innerBounds finishSlots
local notation "B" => core.bound

theorem routines_slots : routines.slots ≤ S := by simp only [slotsAll]; omega
theorem inner_slots : innerBounds.slots ≤ S := by simp only [slotsAll]; omega
theorem finish_slots : finishSlots ≤ S := by simp only [slotsAll]; omega
theorem three_slots : 3 ≤ S := by simp only [slotsAll]; omega
theorem bound_le_T : B ≤ T := by simp only [unitT]; omega
theorem bound_le_W : B ≤ W := by simp only [unitW]; omega
theorem routines_le_T : routines.time ≤ T := by simp only [unitT]; omega
theorem routines_le_W : routines.words ≤ W := by simp only [unitW]; omega
theorem snoc_le_T : core.snocTime ≤ T := by simp only [unitT]; omega
theorem snoc_le_W : core.snocWords ≤ W := by simp only [unitW]; omega
theorem step_le_T : innerBounds.step.time ≤ T := by simp only [unitT]; omega
theorem step_le_W : innerBounds.step.words ≤ W := by simp only [unitW]; omega
theorem initial_le_T : innerBounds.initial.time ≤ T := by simp only [unitT]; omega
theorem initial_le_W : innerBounds.initial.words ≤ W := by simp only [unitW]; omega
theorem finish_le_T : finishTime ≤ T := by simp only [unitT]; omega
theorem finish_le_W : finishWords ≤ W := by simp only [unitW]; omega
theorem one_le_T : 1 ≤ T := by simp only [unitT]; omega
theorem one_le_W : 1 ≤ W := by simp only [unitW]; omega

/-- Close a budget inequality: every atom is a multiple of the bound or a component budget. -/
scoped macro "budget" : tactic => `(tactic| (
  have := core.bound_le_T routines caller innerBounds finishTime; have := core.bound_le_W routines caller innerBounds finishWords
  have := core.routines_le_T routines caller innerBounds finishTime; have := core.routines_le_W routines caller innerBounds finishWords
  have := core.snoc_le_T routines caller innerBounds finishTime; have := core.snoc_le_W routines caller innerBounds finishWords
  have := core.step_le_T routines caller innerBounds finishTime; have := core.step_le_W routines caller innerBounds finishWords
  have := core.initial_le_T routines caller innerBounds finishTime; have := core.initial_le_W routines caller innerBounds finishWords
  have := core.finish_le_T routines caller innerBounds finishTime; have := core.finish_le_W routines caller innerBounds finishWords
  have := core.one_le_T routines caller innerBounds finishTime; have := core.one_le_W routines caller innerBounds finishWords
  have := core.width_pos'
  have hb : core.bound = 5 + 3 * core.width := rfl
  have hwidth := core.width_eq
  have hunit : (DataImplementation.unitLayout w).representation.encoding.words = 0 := rfl
  try simp only [modeTime, modeWords, packetTime, packetWords, appendTime, appendWords] at *
  omega))

theorem outWords_le : core.outWords ≤ B := by unfold bound width; omega
theorem groupRep_le : core.groupRep.encoding.words ≤ B := by
  have := core.groupRep_words; have := core.requestRep_words; unfold bound width; omega
theorem requestRep_le : core.requestRep.encoding.words ≤ B := by unfold bound width; omega
theorem replyRep_le : core.replyRep.encoding.words ≤ B := by unfold bound width; omega
theorem uniformRep_le : core.uniformRep.encoding.words ≤ B := by have := core.requestRep_words; unfold bound width; omega
theorem uniformReply_le : core.uniformReply.encoding.words ≤ B := by have := core.replyRep_words; unfold bound width; omega
theorem keyRep_le : core.keyLayout.representation.encoding.words ≤ B := by
  have := core.groupRep_words; have := core.requestRep_words; unfold bound width; omega
theorem messageRep_le : core.message.representation.encoding.words ≤ B := by unfold bound width; omega
theorem pointRep_le : core.point.representation.encoding.words ≤ B := by unfold bound width; omega
theorem scalarRep_le : core.scalar.representation.encoding.words ≤ B := by unfold bound width; omega
theorem forgeryRep_le : core.forgeryIn.representation.encoding.words ≤ B := by unfold bound width; omega
theorem stateRep_le : core.inner.state.encoding.words ≤ B := by unfold bound width; omega
theorem keyRep'_le : core.inner.key.representation.encoding.words ≤ B := by unfold bound width; omega
theorem pending_le : (CallerStep.pending core.inner.good.control).encoding.words ≤ 2 * B := by
  change core.requestRep.encoding.words + core.inner.state.encoding.words ≤ _
  have := core.requestRep_le; have := core.stateRep_le; omega
theorem next_le : (CallerStep.next core.inner.good.control).encoding.words ≤ 1 + 3 * B := by
  change 1 + max core.forgeryIn.representation.encoding.words (CallerStep.pending core.inner.good.control).encoding.words ≤ _
  have := core.pending_le; have := core.forgeryRep_le; omega
theorem resumeRep_le : (CallerStep.resume core.inner.good.control).encoding.words ≤ 2 * B := by
  change core.inner.state.encoding.words + core.replyRep.encoding.words ≤ _
  have := core.replyRep_le; have := core.stateRep_le; omega

/-! ### Pieces -/
theorem forgeryMessage_boundedBy : core.forgeryMessage.BoundedBy (2000 * T) (2000 * W) :=
  (Implementation.allFirst_boundedBy' _ _ core.messageRep_le).mono (by budget) (by budget)
theorem forgeryMessage_names : NamesAccounted core.forgeryMessage.program.code S := Implementation.allFirst_names _ _ _ _ _

theorem finalRequest_boundedBy : (core.finalRequest routines).BoundedBy (8000 * T) (8000 * W) := by
  unfold finalRequest
  refine (Implementation.BoundedBy.castFunction ((((Implementation.first_boundedBy' _ _ core.forgeryAll_le).then
    (core.forgeryMessage_boundedBy routines caller innerBounds finishTime finishWords)).then routines.hashOfBound).then
    core.hashRequestImpl_boundedBy) _).mono ?_ ?_
  all_goals have := core.groupRep_le; have := core.requestRep_le; have := core.replyRep_le; budget
theorem finalRequest_names : NamesAccounted (core.finalRequest routines).program.code S :=
  Implementation.castFunction_names _ _ ((((Implementation.first_names _ _ _ _ _).seq (core.forgeryMessage_names routines caller innerBounds finishSlots)).seq
    (routines.hashOfNames.mono (core.routines_slots routines caller innerBounds finishSlots))).seq
    ((core.hashRequestImpl_names 0).mono (by simp only [slotsAll]; omega)))

theorem finalState_boundedBy : core.finalState.BoundedBy (30000 * T) (30000 * W) := by
  unfold finalState
  refine (Implementation.BoundedBy.castFunction (Implementation.pair'_boundedBy' _ _ _ _ _ _ _ (Implementation.second_boundedBy' _ _ core.keyed_le)
    ((Implementation.first_boundedBy' _ _ core.forgeryAll_le).then core.modeFinal_boundedBy)
    core.finalInput_le core.keyed_le core.mode_le) _).mono ?_ ?_
  all_goals budget
theorem finalState_names : NamesAccounted core.finalState.program.code S :=
  Implementation.castFunction_names _ _ (Implementation.pair'_names _ _ _ _ _ _ _ (Implementation.second_names _ _ _ _ _)
    ((Implementation.first_names _ _ _ _ _).seq ((core.modeFinal_names 0).mono (by simp only [slotsAll]; omega))))

theorem finalReact_boundedBy : (core.finalReact routines out outLe).BoundedBy (60000 * T) (60000 * W) := by
  unfold finalReact
  refine (Implementation.BoundedBy.castFunction ((Implementation.pair'_boundedBy' _ _ _ _ _ _ _
    (core.finalRequest_boundedBy routines caller innerBounds finishTime finishWords)
    (core.finalState_boundedBy routines caller innerBounds finishTime finishWords)
    core.finalInput_le core.requestAll_le core.wrapper_le).then
    (Implementation.inr_boundedBy' _ _ (core.out_le out outLe) core.pendingWrapper_le)) _).mono ?_ ?_
  all_goals budget
theorem finalReact_names : NamesAccounted (core.finalReact routines out outLe).program.code S :=
  Implementation.castFunction_names _ _ ((Implementation.pair'_names _ _ _ _ _ _ _
    (core.finalRequest_names routines caller innerBounds finishSlots) (core.finalState_names routines caller innerBounds finishSlots)).seq
    ((Implementation.inr_names _ _ _ _).mono (core.three_slots routines caller innerBounds finishSlots)))

theorem reorderPending_boundedBy : core.reorderPending.BoundedBy (40000 * T) (40000 * W) := by
  unfold reorderPending
  refine (Implementation.BoundedBy.castFunction (Implementation.pair'_boundedBy' _ _ _ _ _ _ _
    ((Implementation.first_boundedBy' _ _ core.pendingAll_le).then (Implementation.first_boundedBy' _ _ core.requestAll_le))
    (Implementation.pair'_boundedBy' _ _ _ _ _ _ _
      ((Implementation.first_boundedBy' _ _ core.pendingAll_le).then (Implementation.second_boundedBy' _ _ core.stateAll_le))
      (Implementation.second_boundedBy' _ _ core.keyed_le) core.pendingInput_le core.stateAll_le core.keyed_le)
    core.pendingInput_le core.requestAll_le core.rest_le) _).mono ?_ ?_
  all_goals budget
theorem reorderPending_names : NamesAccounted core.reorderPending.program.code S :=
  Implementation.castFunction_names _ _ (Implementation.pair'_names _ _ _ _ _ _ _
    ((Implementation.first_names _ _ _ _ _).seq (Implementation.first_names _ _ _ _ _))
    (Implementation.pair'_names _ _ _ _ _ _ _ ((Implementation.first_names _ _ _ _ _).seq (Implementation.second_names _ _ _ _ _))
      (Implementation.second_names _ _ _ _ _)))

theorem randomState_boundedBy : core.randomState.BoundedBy (30000 * T) (30000 * W) := by
  unfold randomState
  refine (Implementation.BoundedBy.castFunction (Implementation.pair'_boundedBy' _ _ _ _ _ _ _
    ((Implementation.second_boundedBy' _ _ core.rest_le).then (Implementation.second_boundedBy' _ _ core.keyed_le))
    (((Implementation.second_boundedBy' _ _ core.rest_le).then (Implementation.first_boundedBy' _ _ core.stateAll_le)).then core.modeReady_boundedBy)
    core.randomInput_le core.keyed_le core.mode_le) _).mono ?_ ?_
  all_goals budget
theorem randomState_names : NamesAccounted core.randomState.program.code S :=
  Implementation.castFunction_names _ _ (Implementation.pair'_names _ _ _ _ _ _ _
    ((Implementation.second_names _ _ _ _ _).seq (Implementation.second_names _ _ _ _ _))
    (((Implementation.second_names _ _ _ _ _).seq (Implementation.first_names _ _ _ _ _)).seq
      ((core.modeReady_names 0).mono (by simp only [slotsAll]; omega))))
theorem randomRequestPart_boundedBy : core.randomRequestPart.BoundedBy (6000 * T) (6000 * W) := by
  unfold randomRequestPart
  refine (Implementation.BoundedBy.castFunction ((Implementation.first_boundedBy' _ _ core.uniformAll_le).then core.randomRequestImpl_boundedBy) _).mono ?_ ?_
  all_goals have := core.groupRep_le; have := core.requestRep_le; have := core.replyRep_le; budget
theorem randomRequestPart_names : NamesAccounted core.randomRequestPart.program.code S :=
  Implementation.castFunction_names _ _ ((Implementation.first_names _ _ _ _ _).seq ((core.randomRequestImpl_names 0).mono (by simp only [slotsAll]; omega)))

theorem hashState_boundedBy : core.hashState.BoundedBy (40000 * T) (40000 * W) := by
  unfold hashState
  refine (Implementation.BoundedBy.castFunction (Implementation.pair'_boundedBy' _ _ _ _ _ _ _
    (((Implementation.second_boundedBy' _ _ core.rest_le).then (Implementation.second_boundedBy' _ _ core.keyed_le)).then core.appendOwn_boundedBy)
    (((Implementation.second_boundedBy' _ _ core.rest_le).then (Implementation.first_boundedBy' _ _ core.stateAll_le)).then core.modeReady_boundedBy)
    core.hashInput_le core.keyed_le core.mode_le) _).mono ?_ ?_
  all_goals budget
theorem hashState_names : NamesAccounted core.hashState.program.code S :=
  Implementation.castFunction_names _ _ (Implementation.pair'_names _ _ _ _ _ _ _
    (((Implementation.second_names _ _ _ _ _).seq (Implementation.second_names _ _ _ _ _)).seq (core.appendOwn_names _))
    (((Implementation.second_names _ _ _ _ _).seq (Implementation.first_names _ _ _ _ _)).seq
      ((core.modeReady_names 0).mono (by simp only [slotsAll]; omega))))
theorem hashRequestPart_boundedBy : core.hashRequestPart.BoundedBy (6000 * T) (6000 * W) := by
  unfold hashRequestPart
  refine (Implementation.BoundedBy.castFunction ((Implementation.first_boundedBy' _ _ core.keyAll_le).then core.hashRequestImpl_boundedBy) _).mono ?_ ?_
  all_goals have := core.groupRep_le; have := core.requestRep_le; have := core.replyRep_le; budget
theorem hashRequestPart_names : NamesAccounted core.hashRequestPart.program.code S :=
  Implementation.castFunction_names _ _ ((Implementation.first_names _ _ _ _ _).seq ((core.hashRequestImpl_names 0).mono (by simp only [slotsAll]; omega)))

theorem signRequestPart_boundedBy : (core.signRequestPart routines).BoundedBy (8000 * T) (8000 * W) := by
  unfold signRequestPart
  refine (Implementation.BoundedBy.castFunction (((Implementation.first_boundedBy' _ _ core.messageAll_le).then routines.hashOfBound).then
    core.hashRequestImpl_boundedBy) _).mono ?_ ?_
  all_goals have := core.groupRep_le; have := core.requestRep_le; have := core.replyRep_le; budget
theorem signRequestPart_names : NamesAccounted (core.signRequestPart routines).program.code S :=
  Implementation.castFunction_names _ _ (((Implementation.first_names _ _ _ _ _).seq
    (routines.hashOfNames.mono (core.routines_slots routines caller innerBounds finishSlots))).seq
    ((core.hashRequestImpl_names 0).mono (by simp only [slotsAll]; omega)))
theorem signKey_boundedBy : core.signKey.BoundedBy (2000 * T) (2000 * W) := by
  unfold signKey
  refine (((Implementation.second_boundedBy' _ _ core.rest_le).then (Implementation.second_boundedBy' _ _ core.keyed_le)).then
    (Implementation.first_boundedBy' _ _ core.scalarAll_le)).mono ?_ ?_
  all_goals budget
theorem signKey_names : NamesAccounted core.signKey.program.code S :=
  ((Implementation.second_names _ _ _ _ _).seq (Implementation.second_names _ _ _ _ _)).seq (Implementation.first_names _ _ _ _ _)
theorem signSlots_boundedBy : core.signSlots.BoundedBy (2000 * T) (2000 * W) := by
  unfold signSlots
  refine (((Implementation.second_boundedBy' _ _ core.rest_le).then (Implementation.second_boundedBy' _ _ core.keyed_le)).then
    (Implementation.second_boundedBy' _ _ core.slots_le)).mono ?_ ?_
  all_goals budget
theorem signSlots_names : NamesAccounted core.signSlots.program.code S :=
  ((Implementation.second_names _ _ _ _ _).seq (Implementation.second_names _ _ _ _ _)).seq (Implementation.second_names _ _ _ _ _)
theorem signEntry_boundedBy : (core.signEntry routines).BoundedBy (30000 * T) (30000 * W) := by
  unfold signEntry
  refine (Implementation.BoundedBy.castFunction ((((Implementation.pair'_boundedBy' _ _ _ _ _ _ _
    (core.signKey_boundedBy routines caller innerBounds finishTime finishWords) (Implementation.first_boundedBy' _ _ core.messageAll_le)
    core.signInput_le core.scalarAll_le core.messageAll_le).then routines.corrBound).then
    (Implementation.recast_boundedBy _ _ _ _ _ _)).then (Implementation.inr_boundedBy' _ _ (le_of_eq rfl) core.scalarRep_le)) _).mono ?_ ?_
  all_goals budget
theorem signEntry_names : NamesAccounted (core.signEntry routines).program.code S :=
  Implementation.castFunction_names _ _ ((((Implementation.pair'_names _ _ _ _ _ _ _
    (core.signKey_names routines caller innerBounds finishSlots) (Implementation.first_names _ _ _ _ _)).seq
    (routines.corrNames.mono (core.routines_slots routines caller innerBounds finishSlots))).seq
    (Implementation.recast_names _ _ _ _ _ _ _)).seq ((Implementation.inr_names _ _ _ _).mono (core.three_slots routines caller innerBounds finishSlots)))
theorem signKeyed_boundedBy : (core.signKeyed routines).BoundedBy (100000 * T) (100000 * W) := by
  unfold signKeyed
  refine (Implementation.BoundedBy.castFunction (Implementation.pair'_boundedBy' _ _ _ _ _ _ _
    (core.signKey_boundedBy routines caller innerBounds finishTime finishWords)
    ((Implementation.pair'_boundedBy' _ _ _ _ _ _ _ (core.signEntry_boundedBy routines caller innerBounds finishTime finishWords)
      (core.signSlots_boundedBy routines caller innerBounds finishTime finishWords) core.signInput_le core.slotEntry_le core.slots_le).then
      core.snoc_boundedBy)
    core.signInput_le core.scalarAll_le core.slots_le) _).mono ?_ ?_
  all_goals budget
theorem signKeyed_names : NamesAccounted (core.signKeyed routines).program.code S :=
  Implementation.castFunction_names _ _ (Implementation.pair'_names _ _ _ _ _ _ _
    (core.signKey_names routines caller innerBounds finishSlots)
    ((Implementation.pair'_names _ _ _ _ _ _ _ (core.signEntry_names routines caller innerBounds finishSlots)
      (core.signSlots_names routines caller innerBounds finishSlots)).seq (core.snoc_names _)))
theorem signMode_boundedBy : core.signMode.BoundedBy (30000 * T) (30000 * W) := by
  unfold signMode
  refine (Implementation.BoundedBy.castFunction ((Implementation.pair'_boundedBy' _ _ _ _ _ _ _ (Implementation.first_boundedBy' _ _ core.messageAll_le)
    ((Implementation.second_boundedBy' _ _ core.rest_le).then (Implementation.first_boundedBy' _ _ core.stateAll_le))
    core.signInput_le core.messageAll_le core.stateAll_le).then core.modePreSign_boundedBy) _).mono ?_ ?_
  all_goals budget
theorem signMode_names : NamesAccounted core.signMode.program.code S :=
  Implementation.castFunction_names _ _ ((Implementation.pair'_names _ _ _ _ _ _ _ (Implementation.first_names _ _ _ _ _)
    ((Implementation.second_names _ _ _ _ _).seq (Implementation.first_names _ _ _ _ _))).seq
    ((core.modePreSign_names 0).mono (by simp only [slotsAll]; omega)))
theorem signState_boundedBy : (core.signState routines).BoundedBy (160000 * T) (160000 * W) := by
  unfold signState
  refine (Implementation.BoundedBy.castFunction (Implementation.pair'_boundedBy' _ _ _ _ _ _ _
    (core.signKeyed_boundedBy routines caller innerBounds finishTime finishWords)
    (core.signMode_boundedBy routines caller innerBounds finishTime finishWords) core.signInput_le core.keyed_le core.mode_le) _).mono ?_ ?_
  all_goals budget
theorem signState_names : NamesAccounted (core.signState routines).program.code S :=
  Implementation.castFunction_names _ _ (Implementation.pair'_names _ _ _ _ _ _ _
    (core.signKeyed_names routines caller innerBounds finishSlots) (core.signMode_names routines caller innerBounds finishSlots))

theorem randomReact_boundedBy : (core.randomReact out outLe).BoundedBy (60000 * T) (60000 * W) := by
  unfold randomReact
  refine (Implementation.BoundedBy.castFunction ((Implementation.pair'_boundedBy' _ _ _ _ _ _ _
    (core.randomRequestPart_boundedBy routines caller innerBounds finishTime finishWords)
    (core.randomState_boundedBy routines caller innerBounds finishTime finishWords) core.randomInput_le core.requestAll_le core.wrapper_le).then
    (Implementation.inr_boundedBy' _ _ (core.out_le out outLe) core.pendingWrapper_le)) _).mono ?_ ?_
  all_goals budget
theorem randomReact_names : NamesAccounted (core.randomReact out outLe).program.code S :=
  Implementation.castFunction_names _ _ ((Implementation.pair'_names _ _ _ _ _ _ _
    (core.randomRequestPart_names routines caller innerBounds finishSlots) (core.randomState_names routines caller innerBounds finishSlots)).seq
    ((Implementation.inr_names _ _ _ _).mono (core.three_slots routines caller innerBounds finishSlots)))
theorem hashReact_boundedBy : (core.hashReact out outLe).BoundedBy (80000 * T) (80000 * W) := by
  unfold hashReact
  refine (Implementation.BoundedBy.castFunction ((Implementation.pair'_boundedBy' _ _ _ _ _ _ _
    (core.hashRequestPart_boundedBy routines caller innerBounds finishTime finishWords)
    (core.hashState_boundedBy routines caller innerBounds finishTime finishWords) core.hashInput_le core.requestAll_le core.wrapper_le).then
    (Implementation.inr_boundedBy' _ _ (core.out_le out outLe) core.pendingWrapper_le)) _).mono ?_ ?_
  all_goals budget
theorem hashReact_names : NamesAccounted (core.hashReact out outLe).program.code S :=
  Implementation.castFunction_names _ _ ((Implementation.pair'_names _ _ _ _ _ _ _
    (core.hashRequestPart_names routines caller innerBounds finishSlots) (core.hashState_names routines caller innerBounds finishSlots)).seq
    ((Implementation.inr_names _ _ _ _).mono (core.three_slots routines caller innerBounds finishSlots)))
theorem signReact_boundedBy : (core.signReact routines out outLe).BoundedBy (200000 * T) (200000 * W) := by
  unfold signReact
  refine (Implementation.BoundedBy.castFunction ((Implementation.pair'_boundedBy' _ _ _ _ _ _ _
    (core.signRequestPart_boundedBy routines caller innerBounds finishTime finishWords)
    (core.signState_boundedBy routines caller innerBounds finishTime finishWords) core.signInput_le core.requestAll_le core.wrapper_le).then
    (Implementation.inr_boundedBy' _ _ (core.out_le out outLe) core.pendingWrapper_le)) _).mono ?_ ?_
  all_goals budget
theorem signReact_names : NamesAccounted (core.signReact routines out outLe).program.code S :=
  Implementation.castFunction_names _ _ ((Implementation.pair'_names _ _ _ _ _ _ _
    (core.signRequestPart_names routines caller innerBounds finishSlots) (core.signState_names routines caller innerBounds finishSlots)).seq
    ((Implementation.inr_names _ _ _ _).mono (core.three_slots routines caller innerBounds finishSlots)))

theorem groupReact_boundedBy : (core.groupReact routines out outLe).BoundedBy (320000 * T) (320000 * W) := by
  unfold groupReact
  refine (Implementation.BoundedBy.castFunction (((Implementation.pair'_boundedBy' _ _ _ _ _ _ _
    ((Implementation.first_boundedBy' _ _ core.groupAll_le).then (Implementation.view_boundedBy _ _ _)) (Implementation.second_boundedBy' _ _ core.rest_le)
    core.groupInput_le (Layout.sum_le' _ _ _ _ core.keyAll_le core.messageAll_le) core.rest_le).then
    (Implementation.distribute_boundedBy' _ _ _ core.keyAll_le core.messageAll_le core.rest_le)).then
    (Implementation.branch_boundedBy' _ _ _ _ (core.hashReact_boundedBy routines caller innerBounds out outLe finishTime finishWords)
      (core.signReact_boundedBy routines caller innerBounds out outLe finishTime finishWords) core.hashInput_le core.signInput_le)) _).mono ?_ ?_
  all_goals budget
theorem groupReact_names : NamesAccounted (core.groupReact routines out outLe).program.code S :=
  Implementation.castFunction_names _ _ (((Implementation.pair'_names _ _ _ _ _ _ _
    ((Implementation.first_names _ _ _ _ _).seq (Implementation.view_names _ _ _ _)) (Implementation.second_names _ _ _ _ _)).seq
    ((Implementation.distribute_names _ _ _ _ _).mono (core.three_slots routines caller innerBounds finishSlots))).seq
    (Implementation.branch_names _ _ _ _ (core.hashReact_names routines caller innerBounds out outLe finishSlots)
      (core.signReact_names routines caller innerBounds out outLe finishSlots)))
theorem pendingReact_boundedBy : (core.pendingReact routines out outLe).BoundedBy (500000 * T) (500000 * W) := by
  unfold pendingReact
  refine (Implementation.BoundedBy.castFunction (((core.reorderPending_boundedBy routines caller innerBounds finishTime finishWords).then
    (Implementation.pair'_boundedBy' _ _ _ _ _ _ _ ((Implementation.first_boundedBy' _ _ core.requestAll_le).then (Implementation.view_boundedBy _ _ _))
      (Implementation.second_boundedBy' _ _ core.rest_le) (Layout.prod_le' _ _ _ core.requestAll_le core.rest_le)
      (Layout.sum_le' _ _ _ _ core.uniformAll_le core.groupAll_le) core.rest_le)).then
    ((Implementation.distribute_boundedBy' _ _ _ core.uniformAll_le core.groupAll_le core.rest_le).then
    (Implementation.branch_boundedBy' _ _ _ _ (core.randomReact_boundedBy routines caller innerBounds out outLe finishTime finishWords)
      (core.groupReact_boundedBy routines caller innerBounds out outLe finishTime finishWords) core.randomInput_le core.groupInput_le))) _).mono ?_ ?_
  all_goals budget
theorem pendingReact_names : NamesAccounted (core.pendingReact routines out outLe).program.code S :=
  Implementation.castFunction_names _ _ (((core.reorderPending_names routines caller innerBounds finishSlots).seq
    (Implementation.pair'_names _ _ _ _ _ _ _ ((Implementation.first_names _ _ _ _ _).seq (Implementation.view_names _ _ _ _))
      (Implementation.second_names _ _ _ _ _))).seq
    (((Implementation.distribute_names _ _ _ _ _).mono (core.three_slots routines caller innerBounds finishSlots)).seq
    (Implementation.branch_names _ _ _ _ (core.randomReact_names routines caller innerBounds out outLe finishSlots)
      (core.groupReact_names routines caller innerBounds out outLe finishSlots))))

theorem splitNext_boundedBy : core.splitNext.BoundedBy (10000 * T) (10000 * W) := by
  unfold splitNext
  refine (Implementation.BoundedBy.castFunction ((Implementation.view_boundedBy _ _ _).then
    (Implementation.branch_boundedBy' _ _ _ _ (Implementation.inl_boundedBy' _ _ core.forgeryAll_le core.pendingAll_le)
      ((Implementation.view_boundedBy _ _ _).then (Implementation.inr_boundedBy' _ _ core.forgeryAll_le core.pendingAll_le))
      (Layout.all_le _ core.forgeryRep_le) (Layout.all_le _ core.pending_le))) _).mono ?_ ?_
  all_goals budget
theorem splitNext_names : NamesAccounted core.splitNext.program.code S :=
  Implementation.castFunction_names _ _ ((Implementation.view_names _ _ _ _).seq
    (Implementation.branch_names _ _ _ _ ((Implementation.inl_names _ _ _ _).mono (core.three_slots routines caller innerBounds finishSlots))
      ((Implementation.view_names _ _ _ _).seq ((Implementation.inr_names _ _ _ _).mono (core.three_slots routines caller innerBounds finishSlots)))))
theorem innerStep_boundedBy : (core.innerStep caller).BoundedBy (12000 * T) (12000 * W) := by
  unfold innerStep
  refine (Implementation.BoundedBy.castFunction (((Implementation.view_boundedBy _ _ _).then
    (Implementation.ofRealizer_boundedBy _ innerBounds.localTime innerBounds.localWords)).then
    (core.splitNext_boundedBy routines caller innerBounds finishTime finishWords)) _).mono ?_ ?_
  all_goals budget
theorem innerStep_names : NamesAccounted (core.innerStep caller).program.code S :=
  Implementation.castFunction_names _ _ (((Implementation.view_names _ _ _ _).seq
    ((Implementation.ofRealizer_names _ innerBounds.localNames).mono (core.inner_slots routines caller innerBounds finishSlots))).seq
    (core.splitNext_names routines caller innerBounds finishSlots))
theorem innerInitial_boundedBy : (core.innerInitial caller).BoundedBy (12000 * T) (12000 * W) := by
  unfold innerInitial
  refine (Implementation.BoundedBy.castFunction ((Implementation.ofRealizer_boundedBy _ innerBounds.initialTime innerBounds.initialWords).then
    (core.splitNext_boundedBy routines caller innerBounds finishTime finishWords)) _).mono ?_ ?_
  all_goals budget
theorem innerInitial_names : NamesAccounted (core.innerInitial caller).program.code S :=
  Implementation.castFunction_names _ _ (((Implementation.ofRealizer_names _ innerBounds.initialNames).mono
    (core.inner_slots routines caller innerBounds finishSlots)).seq (core.splitNext_names routines caller innerBounds finishSlots))

theorem post_boundedBy : (core.post routines out outLe).BoundedBy (600000 * T) (600000 * W) := by
  unfold post
  refine (Implementation.BoundedBy.castFunction (((Implementation.swap_boundedBy' _ _ core.keyed_le core.nextSplit_le).then
    (Implementation.distribute_boundedBy' _ _ _ core.forgeryAll_le core.pendingAll_le core.keyed_le)).then
    (Implementation.branch_boundedBy' _ _ _ _ (core.finalReact_boundedBy routines caller innerBounds out outLe finishTime finishWords)
      (core.pendingReact_boundedBy routines caller innerBounds out outLe finishTime finishWords) core.finalInput_le core.pendingInput_le)) _).mono ?_ ?_
  all_goals budget
theorem post_names : NamesAccounted (core.post routines out outLe).program.code S :=
  Implementation.castFunction_names _ _ (((Implementation.swap_names _ _ _ _ _).seq
    ((Implementation.distribute_names _ _ _ _ _).mono (core.three_slots routines caller innerBounds finishSlots))).seq
    (Implementation.branch_names _ _ _ _ (core.finalReact_names routines caller innerBounds out outLe finishSlots)
      (core.pendingReact_names routines caller innerBounds out outLe finishSlots)))


/-! ## Budgets of the step -/
theorem reorderAdvance_boundedBy : core.reorderAdvance.BoundedBy (50000 * T) (50000 * W) := by
  unfold reorderAdvance
  refine (Implementation.BoundedBy.castFunction (Implementation.pair'_boundedBy' _ _ _ _ _ _ _
    ((Implementation.first_boundedBy' _ _ core.wrapper_le).then (Implementation.second_boundedBy' _ _ core.mode_le))
    (Implementation.pair'_boundedBy' _ _ _ _ _ _ _
      ((Implementation.first_boundedBy' _ _ core.wrapper_le).then (Implementation.first_boundedBy' _ _ core.keyed_le))
      (Implementation.second_boundedBy' _ _ core.replyAll_le) core.advanceInput_le core.keyed_le core.replyAll_le)
    core.advanceInput_le core.mode_le core.tailRest_le) _).mono ?_ ?_
  all_goals budget
theorem reorderAdvance_names : NamesAccounted core.reorderAdvance.program.code S :=
  Implementation.castFunction_names _ _ (Implementation.pair'_names _ _ _ _ _ _ _
    ((Implementation.first_names _ _ _ _ _).seq (Implementation.second_names _ _ _ _ _))
    (Implementation.pair'_names _ _ _ _ _ _ _ ((Implementation.first_names _ _ _ _ _).seq (Implementation.first_names _ _ _ _ _))
      (Implementation.second_names _ _ _ _ _)))

section Data
variable {A' : Type} (data : Layout w A') (dataLe : data.representation.encoding.words ≤ core.bound)
theorem replyToFront_boundedBy : (core.replyToFront data dataLe).BoundedBy (50000 * T) (50000 * W) := by
  unfold replyToFront
  refine (Implementation.BoundedBy.castFunction (Implementation.pair'_boundedBy' _ _ _ _ _ _ _
    ((Implementation.second_boundedBy' _ _ core.tailRest_le).then (Implementation.second_boundedBy' _ _ core.replyAll_le))
    (Implementation.pair'_boundedBy' _ _ _ _ _ _ _ (Implementation.first_boundedBy' _ _ dataLe)
      ((Implementation.second_boundedBy' _ _ core.tailRest_le).then (Implementation.first_boundedBy' _ _ core.keyed_le))
      (Layout.prod_le' _ _ _ dataLe core.tailRest_le) dataLe core.keyed_le)
    (Layout.prod_le' _ _ _ dataLe core.tailRest_le) core.replyAll_le (core.dataKeyed_le data dataLe)) _).mono ?_ ?_
  all_goals budget
theorem replyToFront_names : NamesAccounted (core.replyToFront data dataLe).program.code S :=
  Implementation.castFunction_names _ _ (Implementation.pair'_names _ _ _ _ _ _ _
    ((Implementation.second_names _ _ _ _ _).seq (Implementation.second_names _ _ _ _ _))
    (Implementation.pair'_names _ _ _ _ _ _ _ (Implementation.first_names _ _ _ _ _)
      ((Implementation.second_names _ _ _ _ _).seq (Implementation.first_names _ _ _ _ _))))
theorem splitReply_boundedBy : (core.splitReply data dataLe).BoundedBy (50000 * T) (50000 * W) := by
  unfold splitReply
  refine (Implementation.pair'_boundedBy' _ _ _ _ _ _ _
    ((Implementation.first_boundedBy' _ _ core.replyAll_le).then (Implementation.view_boundedBy _ _ _))
    (Implementation.second_boundedBy' _ _ (core.dataKeyed_le data dataLe))
    (core.replyFirst_le data dataLe) (Layout.sum_le' _ _ _ _ core.uniformReplyAll_le core.pointAll_le) (core.dataKeyed_le data dataLe)).mono ?_ ?_
  all_goals budget
theorem splitReply_names : NamesAccounted (core.splitReply data dataLe).program.code S :=
  Implementation.pair'_names _ _ _ _ _ _ _ ((Implementation.first_names _ _ _ _ _).seq (Implementation.view_names _ _ _ _))
    (Implementation.second_names _ _ _ _ _)
end Data

/-! ### The signature reply -/
theorem sigData_boundedBy : core.sigData.BoundedBy (10000 * T) (10000 * W) := by
  unfold sigData
  refine ((Implementation.second_boundedBy' _ _ core.afterKeyed_le).then (Implementation.first_boundedBy' _ _ core.afterHash_le)).mono ?_ ?_
  all_goals budget
theorem sigData_names : NamesAccounted core.sigData.program.code S :=
  (Implementation.second_names _ _ _ _ _).seq (Implementation.first_names _ _ _ _ _)
theorem sigKeyed_boundedBy : core.sigKeyed.BoundedBy (10000 * T) (10000 * W) := by
  unfold sigKeyed
  refine ((Implementation.second_boundedBy' _ _ core.afterKeyed_le).then (Implementation.second_boundedBy' _ _ core.keyed_le)).mono ?_ ?_
  all_goals budget
theorem sigKeyed_names : NamesAccounted core.sigKeyed.program.code S :=
  (Implementation.second_names _ _ _ _ _).seq (Implementation.second_names _ _ _ _ _)
theorem sigKey_boundedBy : core.sigKey.BoundedBy (20000 * T) (20000 * W) := by
  unfold sigKey
  refine ((core.sigKeyed_boundedBy routines caller innerBounds finishTime finishWords).then
    (Implementation.first_boundedBy' _ _ core.scalarAll_le)).mono ?_ ?_
  all_goals budget
theorem sigKey_names : NamesAccounted core.sigKey.program.code S :=
  (core.sigKeyed_names routines caller innerBounds finishSlots).seq (Implementation.first_names _ _ _ _ _)
theorem sigMessage_boundedBy : core.sigMessage.BoundedBy (30000 * T) (30000 * W) := by
  unfold sigMessage
  refine (((core.sigData_boundedBy routines caller innerBounds finishTime finishWords).then
    (Implementation.first_boundedBy' _ _ (Layout.prod_le' _ _ _ core.messageAll_le core.pointAll_le))).then
    (Implementation.first_boundedBy' _ _ core.messageAll_le)).mono ?_ ?_
  all_goals budget
theorem sigMessage_names : NamesAccounted core.sigMessage.program.code S :=
  ((core.sigData_names routines caller innerBounds finishSlots).seq (Implementation.first_names _ _ _ _ _)).seq (Implementation.first_names _ _ _ _ _)
theorem sigHash_boundedBy : core.sigHash.BoundedBy (30000 * T) (30000 * W) := by
  unfold sigHash
  refine (((core.sigData_boundedBy routines caller innerBounds finishTime finishWords).then
    (Implementation.first_boundedBy' _ _ (Layout.prod_le' _ _ _ core.messageAll_le core.pointAll_le))).then
    (Implementation.second_boundedBy' _ _ core.pointAll_le)).mono ?_ ?_
  all_goals budget
theorem sigHash_names : NamesAccounted core.sigHash.program.code S :=
  ((core.sigData_names routines caller innerBounds finishSlots).seq (Implementation.first_names _ _ _ _ _)).seq (Implementation.second_names _ _ _ _ _)
theorem sigState_boundedBy : core.sigState.BoundedBy (20000 * T) (20000 * W) := by
  unfold sigState
  refine ((core.sigData_boundedBy routines caller innerBounds finishTime finishWords).then
    (Implementation.second_boundedBy' _ _ core.stateAll_le)).mono ?_ ?_
  all_goals budget
theorem sigState_names : NamesAccounted core.sigState.program.code S :=
  (core.sigData_names routines caller innerBounds finishSlots).seq (Implementation.second_names _ _ _ _ _)
theorem sigCorrection_boundedBy : (core.sigCorrection routines).BoundedBy (60000 * T) (60000 * W) := by
  unfold sigCorrection
  refine ((Implementation.pair'_boundedBy' _ _ _ _ _ _ _ (core.sigKey_boundedBy routines caller innerBounds finishTime finishWords)
    (core.sigMessage_boundedBy routines caller innerBounds finishTime finishWords) core.sigInput_le core.scalarAll_le core.messageAll_le).then
    routines.corrBound).mono ?_ ?_
  all_goals budget
theorem sigCorrection_names : NamesAccounted (core.sigCorrection routines).program.code S :=
  (Implementation.pair'_names _ _ _ _ _ _ _ (core.sigKey_names routines caller innerBounds finishSlots)
    (core.sigMessage_names routines caller innerBounds finishSlots)).seq
    (routines.corrNames.mono (core.routines_slots routines caller innerBounds finishSlots))
theorem sigPoints_boundedBy : core.sigPoints.BoundedBy (50000 * T) (50000 * W) := by
  unfold sigPoints
  refine (Implementation.pair'_boundedBy' _ _ _ _ _ _ _ (core.sigHash_boundedBy routines caller innerBounds finishTime finishWords)
    (Implementation.first_boundedBy' _ _ core.pointAll_le) core.sigInput_le core.pointAll_le core.pointAll_le).mono ?_ ?_
  all_goals budget
theorem sigPoints_names : NamesAccounted core.sigPoints.program.code S :=
  Implementation.pair'_names _ _ _ _ _ _ _ (core.sigHash_names routines caller innerBounds finishSlots) (Implementation.first_names _ _ _ _ _)
theorem sigCorrected_boundedBy : (core.sigCorrected routines).BoundedBy (150000 * T) (150000 * W) := by
  unfold sigCorrected
  refine ((Implementation.pair'_boundedBy' _ _ _ _ _ _ _ (core.sigCorrection_boundedBy routines caller innerBounds finishTime finishWords)
    (core.sigPoints_boundedBy routines caller innerBounds finishTime finishWords) core.sigInput_le core.scalarAll_le
    (Layout.prod_le' _ _ _ core.pointAll_le core.pointAll_le)).then routines.fmaBound).mono ?_ ?_
  all_goals budget
theorem sigCorrected_names : NamesAccounted (core.sigCorrected routines).program.code S :=
  (Implementation.pair'_names _ _ _ _ _ _ _ (core.sigCorrection_names routines caller innerBounds finishSlots)
    (core.sigPoints_names routines caller innerBounds finishSlots)).seq
    (routines.fmaNames.mono (core.routines_slots routines caller innerBounds finishSlots))
theorem sigResume_boundedBy : (core.sigResume routines).BoundedBy (250000 * T) (250000 * W) := by
  unfold sigResume
  refine (Implementation.pair'_boundedBy' _ _ _ _ _ _ _ (core.sigState_boundedBy routines caller innerBounds finishTime finishWords)
    ((core.sigCorrected_boundedBy routines caller innerBounds finishTime finishWords).then core.pointReply_boundedBy)
    core.sigInput_le core.stateAll_le core.replyAll_le).mono ?_ ?_
  all_goals have := core.groupRep_le; have := core.requestRep_le; have := core.replyRep_le; budget
theorem sigResume_names : NamesAccounted (core.sigResume routines).program.code S :=
  Implementation.pair'_names _ _ _ _ _ _ _ (core.sigState_names routines caller innerBounds finishSlots)
    ((core.sigCorrected_names routines caller innerBounds finishSlots).seq ((core.pointReply_names 0).mono (by simp only [slotsAll]; omega)))

/-! ### The mode branches -/
theorem readyStep_boundedBy : (core.readyStep routines caller out outLe callerReserve).BoundedBy (800000 * T) (800000 * W) := by
  unfold readyStep
  refine (Implementation.BoundedBy.castFunction ((Implementation.pair'_boundedBy' _ _ _ _ _ _ _
    ((Implementation.second_boundedBy' _ _ core.tailRest_le).then (Implementation.first_boundedBy' _ _ core.keyed_le))
    ((Implementation.pair'_boundedBy' _ _ _ _ _ _ _ (Implementation.first_boundedBy' _ _ core.stateAll_le)
      ((Implementation.second_boundedBy' _ _ core.tailRest_le).then (Implementation.second_boundedBy' _ _ core.replyAll_le))
      core.readyInput_le core.stateAll_le core.replyAll_le).then (core.innerStep_boundedBy routines caller innerBounds finishTime finishWords))
    core.readyInput_le core.keyed_le core.nextSplit_le).then
    (core.post_boundedBy routines caller innerBounds out outLe finishTime finishWords)) _).mono ?_ ?_
  all_goals budget
theorem readyStep_names : NamesAccounted (core.readyStep routines caller out outLe callerReserve).program.code S :=
  Implementation.castFunction_names _ _ ((Implementation.pair'_names _ _ _ _ _ _ _
    ((Implementation.second_names _ _ _ _ _).seq (Implementation.first_names _ _ _ _ _))
    ((Implementation.pair'_names _ _ _ _ _ _ _ (Implementation.first_names _ _ _ _ _)
      ((Implementation.second_names _ _ _ _ _).seq (Implementation.second_names _ _ _ _ _))).seq
      (core.innerStep_names routines caller innerBounds finishSlots))).seq
    (core.post_names routines caller innerBounds out outLe finishSlots))

theorem preSignMismatch_boundedBy : (core.preSignMismatch routines out outLe).BoundedBy (120000 * T) (120000 * W) := by
  unfold preSignMismatch
  refine (Implementation.BoundedBy.castFunction ((Implementation.pair'_boundedBy' _ _ _ _ _ _ _
    (((((Implementation.second_boundedBy' _ _ core.preKeyed_le).then (Implementation.first_boundedBy' _ _ core.preSign_le)).then
      (Implementation.first_boundedBy' _ _ core.messageAll_le)).then routines.hashOfBound).then core.hashRequestImpl_boundedBy)
    (Implementation.pair'_boundedBy' _ _ _ _ _ _ _
      ((Implementation.second_boundedBy' _ _ core.preKeyed_le).then (Implementation.second_boundedBy' _ _ core.keyed_le))
      (((Implementation.second_boundedBy' _ _ core.preKeyed_le).then (Implementation.first_boundedBy' _ _ core.preSign_le)).then
        core.modePreSign_boundedBy)
      (Layout.prod_le' _ _ _ core.uniformReplyAll_le core.preKeyed_le) core.keyed_le core.mode_le)
    (Layout.prod_le' _ _ _ core.uniformReplyAll_le core.preKeyed_le) core.requestAll_le core.wrapper_le).then
    (Implementation.inr_boundedBy' _ _ (core.out_le out outLe) core.pendingWrapper_le)) _).mono ?_ ?_
  all_goals have := core.groupRep_le; have := core.requestRep_le; have := core.replyRep_le; budget
theorem preSignMismatch_names : NamesAccounted (core.preSignMismatch routines out outLe).program.code S :=
  Implementation.castFunction_names _ _ ((Implementation.pair'_names _ _ _ _ _ _ _
    (((((Implementation.second_names _ _ _ _ _).seq (Implementation.first_names _ _ _ _ _)).seq (Implementation.first_names _ _ _ _ _)).seq
      (routines.hashOfNames.mono (core.routines_slots routines caller innerBounds finishSlots))).seq
      ((core.hashRequestImpl_names 0).mono (by simp only [slotsAll]; omega)))
    (Implementation.pair'_names _ _ _ _ _ _ _ ((Implementation.second_names _ _ _ _ _).seq (Implementation.second_names _ _ _ _ _))
      (((Implementation.second_names _ _ _ _ _).seq (Implementation.first_names _ _ _ _ _)).seq
        ((core.modePreSign_names 0).mono (by simp only [slotsAll]; omega))))).seq
    ((Implementation.inr_names _ _ _ _).mono (core.three_slots routines caller innerBounds finishSlots)))

theorem preSignHash_boundedBy : (core.preSignHash out outLe).BoundedBy (200000 * T) (200000 * W) := by
  unfold preSignHash
  refine (Implementation.BoundedBy.castFunction ((Implementation.pair'_boundedBy' _ _ _ _ _ _ _
    ((((Implementation.second_boundedBy' _ _ core.preKeyed_le).then (Implementation.first_boundedBy' _ _ core.preSign_le)).then
      (Implementation.first_boundedBy' _ _ core.messageAll_le)).then core.signRequestImpl_boundedBy)
    (Implementation.pair'_boundedBy' _ _ _ _ _ _ _
      ((Implementation.second_boundedBy' _ _ core.preKeyed_le).then (Implementation.second_boundedBy' _ _ core.keyed_le))
      ((Implementation.pair'_boundedBy' _ _ _ _ _ _ _
        (Implementation.pair'_boundedBy' _ _ _ _ _ _ _
          (((Implementation.second_boundedBy' _ _ core.preKeyed_le).then (Implementation.first_boundedBy' _ _ core.preSign_le)).then
            (Implementation.first_boundedBy' _ _ core.messageAll_le))
          (Implementation.first_boundedBy' _ _ core.pointAll_le)
          (Layout.prod_le' _ _ _ core.pointAll_le core.preKeyed_le) core.messageAll_le core.pointAll_le)
        (((Implementation.second_boundedBy' _ _ core.preKeyed_le).then (Implementation.first_boundedBy' _ _ core.preSign_le)).then
          (Implementation.second_boundedBy' _ _ core.stateAll_le))
        (Layout.prod_le' _ _ _ core.pointAll_le core.preKeyed_le) (Layout.prod_le' _ _ _ core.messageAll_le core.pointAll_le) core.stateAll_le).then
        core.modeAfter_boundedBy)
      (Layout.prod_le' _ _ _ core.pointAll_le core.preKeyed_le) core.keyed_le core.mode_le)
    (Layout.prod_le' _ _ _ core.pointAll_le core.preKeyed_le) core.requestAll_le core.wrapper_le).then
    (Implementation.inr_boundedBy' _ _ (core.out_le out outLe) core.pendingWrapper_le)) _).mono ?_ ?_
  all_goals have := core.groupRep_le; have := core.requestRep_le; have := core.replyRep_le; budget
theorem preSignHash_names : NamesAccounted (core.preSignHash out outLe).program.code S :=
  Implementation.castFunction_names _ _ ((Implementation.pair'_names _ _ _ _ _ _ _
    ((((Implementation.second_names _ _ _ _ _).seq (Implementation.first_names _ _ _ _ _)).seq (Implementation.first_names _ _ _ _ _)).seq
      ((core.signRequestImpl_names 0).mono (by simp only [slotsAll]; omega)))
    (Implementation.pair'_names _ _ _ _ _ _ _ ((Implementation.second_names _ _ _ _ _).seq (Implementation.second_names _ _ _ _ _))
      ((Implementation.pair'_names _ _ _ _ _ _ _
        (Implementation.pair'_names _ _ _ _ _ _ _
          (((Implementation.second_names _ _ _ _ _).seq (Implementation.first_names _ _ _ _ _)).seq (Implementation.first_names _ _ _ _ _))
          (Implementation.first_names _ _ _ _ _))
        (((Implementation.second_names _ _ _ _ _).seq (Implementation.first_names _ _ _ _ _)).seq (Implementation.second_names _ _ _ _ _))).seq
        ((core.modeAfter_names 0).mono (by simp only [slotsAll]; omega))))).seq
    ((Implementation.inr_names _ _ _ _).mono (core.three_slots routines caller innerBounds finishSlots)))

theorem preSignReact_boundedBy : (core.preSignReact routines out outLe).BoundedBy (500000 * T) (500000 * W) := by
  unfold preSignReact
  refine (Implementation.BoundedBy.castFunction ((((core.replyToFront_boundedBy routines caller innerBounds finishTime finishWords _ _).then
    (core.splitReply_boundedBy routines caller innerBounds finishTime finishWords _ _)).then
    (Implementation.distribute_boundedBy' _ _ _ core.uniformReplyAll_le core.pointAll_le core.preKeyed_le)).then
    (Implementation.branch_boundedBy' _ _ _ _ (core.preSignMismatch_boundedBy routines caller innerBounds out outLe finishTime finishWords)
      (core.preSignHash_boundedBy routines caller innerBounds out outLe finishTime finishWords)
      (Layout.prod_le' _ _ _ core.uniformReplyAll_le core.preKeyed_le) (Layout.prod_le' _ _ _ core.pointAll_le core.preKeyed_le))) _).mono ?_ ?_
  all_goals budget
theorem preSignReact_names : NamesAccounted (core.preSignReact routines out outLe).program.code S :=
  Implementation.castFunction_names _ _ ((((core.replyToFront_names routines caller innerBounds finishSlots _ _).seq
    (core.splitReply_names routines caller innerBounds finishSlots _ _)).seq
    ((Implementation.distribute_names _ _ _ _ _).mono (core.three_slots routines caller innerBounds finishSlots))).seq
    (Implementation.branch_names _ _ _ _ (core.preSignMismatch_names routines caller innerBounds out outLe finishSlots)
      (core.preSignHash_names routines caller innerBounds out outLe finishSlots)))

theorem afterMismatch_boundedBy : (core.afterMismatch out outLe).BoundedBy (120000 * T) (120000 * W) := by
  unfold afterMismatch
  refine (Implementation.BoundedBy.castFunction ((Implementation.pair'_boundedBy' _ _ _ _ _ _ _
    (((((Implementation.second_boundedBy' _ _ core.afterKeyed_le).then (Implementation.first_boundedBy' _ _ core.afterHash_le)).then
      (Implementation.first_boundedBy' _ _ (Layout.prod_le' _ _ _ core.messageAll_le core.pointAll_le))).then
      (Implementation.first_boundedBy' _ _ core.messageAll_le)).then core.signRequestImpl_boundedBy)
    (Implementation.pair'_boundedBy' _ _ _ _ _ _ _
      ((Implementation.second_boundedBy' _ _ core.afterKeyed_le).then (Implementation.second_boundedBy' _ _ core.keyed_le))
      (((Implementation.second_boundedBy' _ _ core.afterKeyed_le).then (Implementation.first_boundedBy' _ _ core.afterHash_le)).then
        core.modeAfter_boundedBy)
      (Layout.prod_le' _ _ _ core.uniformReplyAll_le core.afterKeyed_le) core.keyed_le core.mode_le)
    (Layout.prod_le' _ _ _ core.uniformReplyAll_le core.afterKeyed_le) core.requestAll_le core.wrapper_le).then
    (Implementation.inr_boundedBy' _ _ (core.out_le out outLe) core.pendingWrapper_le)) _).mono ?_ ?_
  all_goals have := core.groupRep_le; have := core.requestRep_le; have := core.replyRep_le; budget
theorem afterMismatch_names : NamesAccounted (core.afterMismatch out outLe).program.code S :=
  Implementation.castFunction_names _ _ ((Implementation.pair'_names _ _ _ _ _ _ _
    (((((Implementation.second_names _ _ _ _ _).seq (Implementation.first_names _ _ _ _ _)).seq (Implementation.first_names _ _ _ _ _)).seq
      (Implementation.first_names _ _ _ _ _)).seq ((core.signRequestImpl_names 0).mono (by simp only [slotsAll]; omega)))
    (Implementation.pair'_names _ _ _ _ _ _ _ ((Implementation.second_names _ _ _ _ _).seq (Implementation.second_names _ _ _ _ _))
      (((Implementation.second_names _ _ _ _ _).seq (Implementation.first_names _ _ _ _ _)).seq
        ((core.modeAfter_names 0).mono (by simp only [slotsAll]; omega))))).seq
    ((Implementation.inr_names _ _ _ _).mono (core.three_slots routines caller innerBounds finishSlots)))

theorem afterSig_boundedBy : (core.afterSig routines caller out outLe callerReserve).BoundedBy (1000000 * T) (1000000 * W) := by
  unfold afterSig
  refine (Implementation.BoundedBy.castFunction ((Implementation.pair'_boundedBy' _ _ _ _ _ _ _
    (core.sigKeyed_boundedBy routines caller innerBounds finishTime finishWords)
    ((core.sigResume_boundedBy routines caller innerBounds finishTime finishWords).then
      (core.innerStep_boundedBy routines caller innerBounds finishTime finishWords))
    core.sigInput_le core.keyed_le core.nextSplit_le).then
    (core.post_boundedBy routines caller innerBounds out outLe finishTime finishWords)) _).mono ?_ ?_
  all_goals budget
theorem afterSig_names : NamesAccounted (core.afterSig routines caller out outLe callerReserve).program.code S :=
  Implementation.castFunction_names _ _ ((Implementation.pair'_names _ _ _ _ _ _ _ (core.sigKeyed_names routines caller innerBounds finishSlots)
    ((core.sigResume_names routines caller innerBounds finishSlots).seq (core.innerStep_names routines caller innerBounds finishSlots))).seq
    (core.post_names routines caller innerBounds out outLe finishSlots))

theorem afterReact_boundedBy : (core.afterReact routines caller out outLe callerReserve).BoundedBy (1300000 * T) (1300000 * W) := by
  unfold afterReact
  refine (Implementation.BoundedBy.castFunction ((((core.replyToFront_boundedBy routines caller innerBounds finishTime finishWords _ _).then
    (core.splitReply_boundedBy routines caller innerBounds finishTime finishWords _ _)).then
    (Implementation.distribute_boundedBy' _ _ _ core.uniformReplyAll_le core.pointAll_le core.afterKeyed_le)).then
    (Implementation.branch_boundedBy' _ _ _ _ (core.afterMismatch_boundedBy routines caller innerBounds out outLe finishTime finishWords)
      (core.afterSig_boundedBy routines caller innerBounds out outLe finishTime finishWords callerReserve)
      (Layout.prod_le' _ _ _ core.uniformReplyAll_le core.afterKeyed_le) core.sigInput_le)) _).mono ?_ ?_
  all_goals budget
theorem afterReact_names : NamesAccounted (core.afterReact routines caller out outLe callerReserve).program.code S :=
  Implementation.castFunction_names _ _ ((((core.replyToFront_names routines caller innerBounds finishSlots _ _).seq
    (core.splitReply_names routines caller innerBounds finishSlots _ _)).seq
    ((Implementation.distribute_names _ _ _ _ _).mono (core.three_slots routines caller innerBounds finishSlots))).seq
    (Implementation.branch_names _ _ _ _ (core.afterMismatch_names routines caller innerBounds out outLe finishSlots)
      (core.afterSig_names routines caller innerBounds out outLe finishSlots callerReserve)))

include finishBound in
theorem finalModeReact_boundedBy : (core.finalModeReact out outLe finish).BoundedBy (60000 * T) (60000 * W) := by
  unfold finalModeReact
  refine (Implementation.BoundedBy.castFunction (((Implementation.pair'_boundedBy' _ _ _ _ _ _ _
    (Implementation.first_boundedBy' _ _ core.forgeryAll_le)
    ((Implementation.second_boundedBy' _ _ core.tailRest_le).then (Implementation.first_boundedBy' _ _ core.keyed_le))
    core.finalModeInput_le core.forgeryAll_le core.keyed_le).then finishBound).then
    (Implementation.inl_boundedBy' _ _ (core.out_le out outLe) core.pendingWrapper_le)) _).mono ?_ ?_
  all_goals budget
include finishNames in
theorem finalModeReact_names : NamesAccounted (core.finalModeReact out outLe finish).program.code S :=
  Implementation.castFunction_names _ _ (((Implementation.pair'_names _ _ _ _ _ _ _ (Implementation.first_names _ _ _ _ _)
    ((Implementation.second_names _ _ _ _ _).seq (Implementation.first_names _ _ _ _ _))).seq
    (finishNames.mono (core.finish_slots routines caller innerBounds finishSlots))).seq
    ((Implementation.inl_names _ _ _ _).mono (core.three_slots routines caller innerBounds finishSlots)))

include finishBound in
theorem tail₂React_boundedBy : (core.tail₂React routines caller out outLe finish callerReserve).BoundedBy (1500000 * T) (1500000 * W) := by
  unfold tail₂React
  refine (Implementation.BoundedBy.castFunction ((Implementation.distribute_boundedBy' _ _ _ core.afterHash_le core.forgeryAll_le core.tailRest_le).then
    (Implementation.branch_boundedBy' _ _ _ _ (core.afterReact_boundedBy routines caller innerBounds out outLe finishTime finishWords callerReserve)
      (core.finalModeReact_boundedBy routines caller innerBounds out outLe finish finishTime finishWords finishBound)
      core.afterInput_le core.finalModeInput_le)) _).mono ?_ ?_
  all_goals budget
include finishNames in
theorem tail₂React_names : NamesAccounted (core.tail₂React routines caller out outLe finish callerReserve).program.code S :=
  Implementation.castFunction_names _ _ (((Implementation.distribute_names _ _ _ _ _).mono (core.three_slots routines caller innerBounds finishSlots)).seq
    (Implementation.branch_names _ _ _ _ (core.afterReact_names routines caller innerBounds out outLe finishSlots callerReserve)
      (core.finalModeReact_names routines caller innerBounds out outLe finish finishSlots finishNames)))

include finishBound in
theorem tail₁React_boundedBy : (core.tail₁React routines caller out outLe finish callerReserve).BoundedBy (2100000 * T) (2100000 * W) := by
  unfold tail₁React
  refine (Implementation.BoundedBy.castFunction ((Implementation.distribute_boundedBy' _ _ _ core.preSign_le core.tail₂_le core.tailRest_le).then
    (Implementation.branch_boundedBy' _ _ _ _ (core.preSignReact_boundedBy routines caller innerBounds out outLe finishTime finishWords)
      (core.tail₂React_boundedBy routines caller innerBounds out outLe finish finishTime finishWords finishBound callerReserve)
      core.preSignInput_le core.tail₂Input_le)) _).mono ?_ ?_
  all_goals budget
include finishNames in
theorem tail₁React_names : NamesAccounted (core.tail₁React routines caller out outLe finish callerReserve).program.code S :=
  Implementation.castFunction_names _ _ (((Implementation.distribute_names _ _ _ _ _).mono (core.three_slots routines caller innerBounds finishSlots)).seq
    (Implementation.branch_names _ _ _ _ (core.preSignReact_names routines caller innerBounds out outLe finishSlots)
      (core.tail₂React_names routines caller innerBounds out outLe finish finishSlots finishNames callerReserve)))

include finishBound in
/-- The step's budget. -/
theorem advanceImpl_boundedBy : (core.advanceImpl routines caller out outLe finish callerReserve).BoundedBy (3000000 * T) (3000000 * W) := by
  unfold advanceImpl
  refine (Implementation.BoundedBy.castFunction (((core.reorderAdvance_boundedBy routines caller innerBounds finishTime finishWords).then
    (Implementation.distribute_boundedBy' _ _ _ core.stateAll_le core.tail₁_le core.tailRest_le)).then
    (Implementation.branch_boundedBy' _ _ _ _ (core.readyStep_boundedBy routines caller innerBounds out outLe finishTime finishWords callerReserve)
      (core.tail₁React_boundedBy routines caller innerBounds out outLe finish finishTime finishWords finishBound callerReserve)
      core.readyInput_le core.tail₁Input_le)) _).mono ?_ ?_
  all_goals budget
include finishNames in
theorem advanceImpl_names : NamesAccounted (core.advanceImpl routines caller out outLe finish callerReserve).program.code S :=
  Implementation.castFunction_names _ _ (((core.reorderAdvance_names routines caller innerBounds finishSlots).seq
    ((Implementation.distribute_names _ _ _ _ _).mono (core.three_slots routines caller innerBounds finishSlots))).seq
    (Implementation.branch_names _ _ _ _ (core.readyStep_names routines caller innerBounds out outLe finishSlots callerReserve)
      (core.tail₁React_names routines caller innerBounds out outLe finish finishSlots finishNames callerReserve)))

/-! ### Initialization -/
theorem emptySlots_boundedBy : core.emptySlots.BoundedBy (10000 * T) (10000 * W) :=
  (Implementation.constant_bounded' _ _ core.slots_le).mono (by budget) (by budget)
theorem emptySlots_names : NamesAccounted core.emptySlots.program.code S := Implementation.constant_names _ _ _ _ _
/-- The initialization's budget. -/
theorem initialImpl_boundedBy : (core.initialImpl routines caller out outLe initialReserve).BoundedBy (900000 * T) (900000 * W) := by
  unfold initialImpl
  refine (Implementation.BoundedBy.castFunction ((Implementation.pair'_boundedBy' _ _ _ _ _ _ _
    (Implementation.pair'_boundedBy' _ _ _ _ _ _ _ (Implementation.allSecond_boundedBy' _ _ core.scalarRep_le)
      (core.emptySlots_boundedBy routines caller innerBounds finishTime finishWords) core.keyAll'_le core.scalarAll_le core.slots_le)
    ((Implementation.allFirst_boundedBy' _ _ core.keyRep'_le).then (core.innerInitial_boundedBy routines caller innerBounds finishTime finishWords))
    core.keyAll'_le core.keyed_le core.nextSplit_le).then
    (core.post_boundedBy routines caller innerBounds out outLe finishTime finishWords)) _).mono ?_ ?_
  all_goals budget
theorem initialImpl_names : NamesAccounted (core.initialImpl routines caller out outLe initialReserve).program.code S :=
  Implementation.castFunction_names _ _ ((Implementation.pair'_names _ _ _ _ _ _ _
    (Implementation.pair'_names _ _ _ _ _ _ _ (Implementation.allSecond_names _ _ _ _ _) (core.emptySlots_names routines caller innerBounds finishSlots))
    ((Implementation.allFirst_names _ _ _ _ _).seq (core.innerInitial_names routines caller innerBounds finishSlots))).seq
    (core.post_names routines caller innerBounds out outLe finishSlots))

end Core

end Signatures.Runtime.CaliperBackend.SyncWrap
