import Proofs.Runtime.Caliper.SyncWrapCaller
import Proofs.SynchronizedPS.WrapMachine

/-! The wrapper caller corresponds to the wrapper machine around the inner caller's machine.
The caller's modes are the machine's states, with the inner caller's state view inside; the
domain carries the inner caller's domain together with the inner program's remaining query
bound, so the inner caller can always be stepped, and room in the slot list. -/
namespace Signatures.Runtime.CaliperBackend.SyncWrap
open Caliper BoundedSource WeightedFull OracleComp OracleSpec Model.LazyAGM SynchronizedPS.Wrapped
open PFunctor PFunctor.DynSystem PFunctor.DynSystem.DynComputation

set_option linter.unusedSectionVars false

variable {w : Nat} {Atom : Type} {base : Atom → Type} {key scalar : Ty Atom} {G PK A : Type}
  [Field (scalar.Value base)] [AddCommGroup G] [Module (scalar.Value base) G] [DecidableEq (key.Value base)]
  {core : Core w (key.Value base) (key.Value base × scalar.Value base) G (scalar.Value base) PK A}
  (routines : Routines core) (caller : SharedCaller core.inner)
  (wrapper : Wrapper core) (outLe : wrapper.outer.good.forgery.representation.encoding.words ≤ core.outWords)
  {finishFn : core.forgeryIn.Value × (core.scalar.Value × List (Unit ⊕ scalar.Value base)) →
    (key.Value base × scalar.Value base) × (scalar.Value base × (List (scalar.Value base) × List (scalar.Value base)))}
  (finish : Implementation .unit core.finalInput wrapper.outer.good.forgery finishFn)
  (callerReserve : caller.continuation.code.memBound + 50 < 2 ^ w)
  (initialReserve : caller.initialCode.code.memBound + 50 < 2 ^ w)
  (messageTotal : ∀ m, core.message.valid m)
  (hashOfLaw : ∀ m, (routines.hashOfFn m).val = m.val.1)
  (fmaLaw : ∀ c h σ, (routines.fmaFn (c, (h, σ))).val = σ.val + c.val • h.val)
  (fuel : Nat) (invariant : Invariant core.inner.good core.inner.goodSetup caller fuel)
  (witness : Correspondence core.inner.good core.inner.goodSetup caller fuel invariant (Equiv.refl (key.Value base)))

local notation "Request" => core.inner.good.Request
local notation "RequestOut" => wrapper.outer.good.Request
local notation "queryIn" => WeightedCallerHandler.queryIn core.inner.good.service core.inner.good.randomBound (Equiv.symm (Equiv.refl (key.Value base)))
local notation "replyMatchesIn" => WeightedCallerHandler.replyMatchesIn core.inner.good.service core.inner.good.randomBound (Equiv.symm (Equiv.refl (key.Value base)))
local notation "queryOut" => WeightedCallerHandler.queryIn wrapper.outer.good.service wrapper.outer.good.randomBound (Equiv.symm (Equiv.refl (key.Value base)))
local notation "replyMatchesOut" => WeightedCallerHandler.replyMatchesIn wrapper.outer.good.service wrapper.outer.good.randomBound (Equiv.symm (Equiv.refl (key.Value base)))
local notation "replyMatchesOut'" => WeightedCallerHandler.replyMatches wrapper.outer.good.service wrapper.outer.good.randomBound

namespace Wrapper

/-! ## The machine -/

/-- The known key read from a raw key input; invalid inputs never occur. -/
noncomputable def proj (u : PK × scalar.Value base) : core.scalar.Value :=
  by classical exact if h : core.scalar.valid u.2 then ⟨u.2, h⟩ else ⟨0, core.inner.scheme.zeroValid⟩

theorem proj_val (u : core.key.Value) : proj (core := core) u.val = ⟨u.val.2, u.property.2⟩ := by
  unfold proj
  rw [dite_eq_left_of_eq_true (eq_true u.property.2)]

/-- The correction scalar on a raw message. -/
def corr (d : core.scalar.Value) (m : key.Value base × scalar.Value base) : scalar.Value base :=
  (routines.corrFn (d, ⟨m, messageTotal m⟩)).val
theorem corr_val (d : core.scalar.Value) (m : core.message.Value) : corr routines messageTotal d m.val = (routines.corrFn (d, m)).val := rfl

/-- The slot entry of an attacker event. -/
def mark (d : core.scalar.Value) : Event (scalar.Value base) (key.Value base) → Unit ⊕ scalar.Value base
  | .hash _ => own _
  | .sign m => .inr (corr routines messageTotal d m)

def finalIndex (result : core.forgeryIn.Value) : key.Value base := result.val.1.1

/-- The wrapped forgery; a slot list without room never occurs. -/
noncomputable def fin (d : core.scalar.Value) (result : core.forgeryIn.Value) (marks : List (Unit ⊕ scalar.Value base)) :
    wrapper.outer.good.forgery.Value := by
  classical
  exact if h : core.slots.valid marks then ⟨finishFn (result, (d, marks)), finish.preserves _ ⟨trivial, trivial, h⟩⟩
    else ⟨finishFn (result, (d, [])), finish.preserves _ ⟨trivial, trivial, by simp [Layout.boundedList]⟩⟩

theorem fin_of_valid (d : core.scalar.Value) (result : core.forgeryIn.Value) (marks : List (Unit ⊕ scalar.Value base))
    (valid : core.slots.valid marks) :
    (wrapper.fin finish d result marks).val = finishFn (result, (d, marks)) := by
  unfold fin
  rw [dite_eq_left_of_eq_true (eq_true valid)]

/-- The wrapper machine around the inner correspondence's machine. -/
@[reducible] noncomputable def machine : OracleMachine (advSpec (key.Value base) (key.Value base × scalar.Value base) G) (PK × scalar.Value base)
    wrapper.outer.good.forgery.Value :=
  SynchronizedPS.Wrapped.machine witness.machine Prod.fst proj (corr routines messageTotal) (mark routines messageTotal) finalIndex (wrapper.fin finish)

/-- The machine state of a caller state. -/
def stateView (value : RequestOut × core.wrapper.Value) : (wrapper.machine routines caller finish messageTotal fuel invariant witness).State :=
  match value.2.val.2 with
  | .inl a => (value.2.val.1.1, .ready (witness.stateView (value.1, a)) value.2.val.1.2)
  | .inr (.inl (m, a)) => (value.2.val.1.1, .ready (witness.stateView (.inr (.inr m), a)) value.2.val.1.2)
  | .inr (.inr (.inl ((m, h), a))) => (value.2.val.1.1, .gotHash (witness.stateView (.inr (.inr m), a)) h.val value.2.val.1.2)
  | .inr (.inr (.inr forged)) => (value.2.val.1.1, .final forged value.2.val.1.2)

/-! ## The domain -/

/-- The inner caller is pending `(q, a)` with a bounded residual program in its domain. -/
def Inner (q : Request) (a : A) : Prop :=
  CallerMachine.Matches witness.machine queryIn witness.stateView (.inr (q, a)) (witness.stateView (q, a)) ∧
  ∃ (P : OracleComp (advSpec (key.Value base) (key.Value base × scalar.Value base) G) core.forgeryIn.Value) (n : Nat),
    witness.machine.toDynSystem.behavior (witness.stateView (q, a)) = FreeM.toResumption P ∧ P.IsTotalRollBound n ∧
    invariant.domain n (q, a)

def domain (remaining : Nat) (value : RequestOut × core.wrapper.Value) : Prop :=
  value.2.val.1.2.length + remaining ≤ core.slotCap ∧
  match value.2.val.2 with
  | .inl a => Inner caller fuel invariant witness value.1 a
  | .inr (.inl (m, a)) => value.1 = core.hashRequest (routines.hashOfFn m) ∧ Inner caller fuel invariant witness (.inr (.inr m)) a
  | .inr (.inr (.inl ((m, _), a))) => value.1 = core.signRequest m ∧ Inner caller fuel invariant witness (.inr (.inr m)) a
  | .inr (.inr (.inr forged)) => value.1 = core.hashRequest (routines.hashOfFn ⟨forged.val.1, forged.property.1⟩)

/-- What an inner step yields: a returned forgery seen by the machine, or a pending pair whose
machine state is its view and which is again in the domain. -/
def After : core.forgeryIn.Value ⊕ (Request × A) → witness.machine.State → Prop
  | .inl forged, s => witness.machine.view s = .inl forged
  | .inr (q, a), s => s = witness.stateView (q, a) ∧ Inner caller fuel invariant witness q a

/-- The original-key reply relation is the handler's with the identity key decoding. -/
theorem replyMatches_of_in (q : Request) (represented : core.inner.good.Reply)
    (original : (advSpec (key.Value base) (key.Value base × scalar.Value base) G).Range (queryIn q))
    (h : replyMatchesIn q represented original) :
    WeightedCallerHandler.replyMatches core.inner.good.service core.inner.good.randomBound q represented original := by
  rcases q with n | (index | message) <;> exact h

/-- Stepping the inner caller from a pending pair in the domain. -/
theorem inner_step {q : Request} {a : A} (h : Inner caller fuel invariant witness q a)
    (represented : core.inner.good.Reply) (original : (advSpec (key.Value base) (key.Value base × scalar.Value base) G).Range (queryIn q))
    (matched : replyMatchesIn q represented original) :
    ∃ next, witness.machine.view (witness.stateView (q, a)) = .inr ⟨queryIn q, next⟩ ∧
      After caller fuel invariant witness (caller.advance (a, represented)) (next original) := by
  obtain ⟨matched₀, P, n, hb, hn, hdom⟩ := h
  cases matched₀ with
  | pending _ _ next view =>
    obtain ⟨k, rfl, hk⟩ := Model.Machine.exists_liftBind_of_view_inr _ hb view
    rw [FreeM.isTotalRollBound_liftBind_iff] at hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have valid := invariant.advanceValid m q a hdom represented original (replyMatches_of_in q represented original matched)
    have matched' := witness.advanceMatches m q a hdom next view represented original matched
    refine ⟨next, view, ?_⟩
    rcases hadv : caller.advance (a, represented) with forged | ⟨q', a'⟩
    · rw [hadv] at matched'
      cases matched' with
      | returned _ _ view' => exact view'
    · rw [hadv] at matched' valid
      generalize hs : next original = s at matched'
      cases matched' with
      | pending _ _ next' view' =>
        exact ⟨rfl, .pending q' a' next' view', k original, m, by rw [← hs]; exact hk original, by simpa using hn.2 original, valid⟩


/-! ## Views of the wrapper machine -/

theorem view_eq (st : core.scalar.Value × SynchronizedPS.Wrapped.Core witness.machine.State core.forgeryIn.Value (Unit ⊕ scalar.Value base) G) :
    (wrapper.machine routines caller finish messageTotal fuel invariant witness).view st =
      SynchronizedPS.Wrapped.step witness.machine (corr routines messageTotal) (mark routines messageTotal) finalIndex (wrapper.fin finish) st := by
  simp [machine, SynchronizedPS.Wrapped.machine]

theorem queryIn_random (n : Fin (core.inner.good.randomBound + 1)) : queryIn (.inl n) = .inl (.inl n.val) := rfl
theorem queryIn_hash (index : core.keyLayout.Value) : queryIn (.inr (.inl index)) = .inl (.inr index.val) := by
  simp [WeightedCallerHandler.queryIn]
theorem queryIn_hashRequest (index : core.keyLayout.Value) : queryIn (core.hashRequest index) = .inl (.inr index.val) := queryIn_hash index
include hashOfLaw in
theorem queryIn_hashOf (m : core.message.Value) : queryIn (core.hashRequest (routines.hashOfFn m)) = .inl (.inr m.val.1) := by
  rw [queryIn_hashRequest, hashOfLaw]
theorem queryIn_sign (m : core.message.Value) : queryIn (.inr (.inr m)) = .inr m.val := rfl
theorem queryIn_signRequest (m : core.message.Value) : queryIn (core.signRequest m) = .inr m.val := rfl

theorem pendingEvent_random (n : Fin (core.inner.good.randomBound + 1)) (next : _ → witness.machine.State) :
    SynchronizedPS.Wrapped.pendingEvent witness.machine (.inr ⟨queryIn (.inl n), next⟩) = [] := rfl
theorem pendingEvent_hash (index : core.keyLayout.Value) (next : _ → witness.machine.State) :
    SynchronizedPS.Wrapped.pendingEvent witness.machine (.inr ⟨queryIn (.inr (.inl index)), next⟩) = [.hash index.val] := rfl
theorem pendingEvent_sign (m : core.message.Value) (next : _ → witness.machine.State) :
    SynchronizedPS.Wrapped.pendingEvent witness.machine (.inr ⟨queryIn (.inr (.inr m)), next⟩) = [.sign m.val] := rfl

omit [AddCommGroup G] [Module (scalar.Value base) G] in
/-- Hash queries with equal periods and one continuation are one query node. -/
theorem sigma_hash_congr {S : Type} {x y : key.Value base} (f : G → S) (h : x = y) :
    (⟨.inl (.inr x), f⟩ : (advSpec (key.Value base) (key.Value base × scalar.Value base) G).toPFunctor.Obj S) = ⟨.inl (.inr y), f⟩ := by
  cases h; rfl

/-- Two views of one state have the same continuation. -/
theorem next_eq {S : Type} {x : wrapper.outer.good.forgery.Value ⊕ (advSpec (key.Value base) (key.Value base × scalar.Value base) G).toPFunctor.Obj S}
    {a : (advSpec (key.Value base) (key.Value base × scalar.Value base) G).Domain} {next next' : _ → S}
    (h : x = .inr ⟨a, next⟩) (h' : x = .inr ⟨a, next'⟩) : next = next' :=
  eq_of_heq (Sigma.mk.inj_iff.mp (Sum.inr.inj (h.symm.trans h'))).2

/-- The outer caller's reply relations are the inner handler's, request by request. -/
theorem in_of_random (n : Fin (core.inner.good.randomBound + 1)) (represented : core.inner.good.Reply) (original : Fin (n.val + 1))
    (h : replyMatchesOut' (.inl n) represented original) : replyMatchesIn (.inl n) represented original := by
  rcases represented with packet | point <;> exact h
theorem in_of_hash (index : core.keyLayout.Value) (represented : core.inner.good.Reply) (original : G)
    (h : replyMatchesOut' (.inr (.inl index)) represented original) : replyMatchesIn (.inr (.inl index)) represented original := by
  rcases represented with packet | point <;> exact h
theorem in_of_sign (m : core.message.Value) (represented : core.inner.good.Reply) (original : G)
    (h : replyMatchesOut' (.inr (.inr m)) represented original) : replyMatchesIn (.inr (.inr m)) represented original := by
  rcases represented with packet | point <;> exact h
theorem in_of_random' (n : Fin (core.inner.good.randomBound + 1)) (represented : core.inner.good.Reply) (original : Fin (n.val + 1))
    (h : replyMatchesOut (.inl n) represented original) : replyMatchesIn (.inl n) represented original := by
  rcases represented with packet | point <;> exact h
theorem in_of_hash' (index : core.keyLayout.Value) (represented : core.inner.good.Reply) (original : G)
    (h : replyMatchesOut (.inr (.inl index)) represented original) : replyMatchesIn (.inr (.inl index)) represented original := by
  rcases represented with packet | point <;> exact h
theorem in_of_sign' (m : core.message.Value) (represented : core.inner.good.Reply) (original : G)
    (h : replyMatchesOut (.inr (.inr m)) represented original) : replyMatchesIn (.inr (.inr m)) represented original := by
  rcases represented with packet | point <;> exact h

/-- A matched reply to a hash or signing request is a point with the original value. -/
theorem point_of_hash (index : core.keyLayout.Value) (represented : core.inner.good.Reply) (original : G)
    (matched : replyMatchesIn (.inr (.inl index)) represented original) :
    ∃ point : core.point.Value, represented = .inr point ∧ point.val = original := by
  rcases represented with packet | point
  · exact absurd matched (by simp [WeightedCallerHandler.replyMatchesIn, WeightedCallerHandler.replyValue, WeightedCallerHandler.answerIn])
  · exact ⟨point, rfl, by simpa [WeightedCallerHandler.replyMatchesIn, WeightedCallerHandler.replyValue, WeightedCallerHandler.answerIn] using matched⟩
theorem point_of_sign (m : core.message.Value) (represented : core.inner.good.Reply) (original : G)
    (matched : replyMatchesIn (.inr (.inr m)) represented original) :
    ∃ point : core.point.Value, represented = .inr point ∧ point.val = original := by
  rcases represented with packet | point
  · exact absurd matched (by simp [WeightedCallerHandler.replyMatchesIn, WeightedCallerHandler.replyValue, WeightedCallerHandler.answerIn])
  · exact ⟨point, rfl, by simpa [WeightedCallerHandler.replyMatchesIn, WeightedCallerHandler.replyValue, WeightedCallerHandler.answerIn] using matched⟩
include fmaLaw in
/-- The corrected signature matches the original reply after the correction. -/
theorem corrected_matches (k : core.scalar.Value) (m : core.message.Value) (h σ : core.point.Value) :
    replyMatchesIn (.inr (.inr m)) (.inr (routines.fmaFn (routines.corrFn (k, m), (h, σ)))) (σ.val + corr routines messageTotal k m.val • h.val) := by
  simp [WeightedCallerHandler.replyMatchesIn, WeightedCallerHandler.replyValue, WeightedCallerHandler.answerIn, fmaLaw, corr]

theorem append_eq (entry : Unit ⊕ scalar.Value base) (slots : List (Unit ⊕ scalar.Value base)) (room : slots.length < core.slotCap) :
    core.append (entry, slots) = slots ++ [entry] := by
  simp [Core.append, room]

/-! ## After an inner step -/

variable (remaining : Nat)

/-- The wrapper's reaction keeps the domain. -/
theorem post_domain (k : core.scalar.Value) (slots : List (Unit ⊕ scalar.Value base)) (room : slots.length + remaining + 1 ≤ core.slotCap)
    (head : core.forgeryIn.Value ⊕ (Request × A)) (s : witness.machine.State) (after : After caller fuel invariant witness head s)
    (p : (core.output wrapper.outer.good.forgery outLe).valid (core.postFn routines ((k, slots), head))) :
    WeightedCaller.HeadValid wrapper.outer.good.service wrapper.outer.good.randomBound (domain routines caller wrapper fuel invariant witness) remaining
      (wrapper.toNext outLe ⟨core.postFn routines ((k, slots), head), p⟩) := by
  rcases head with forged | ⟨n | index | m, a⟩
  · exact ⟨by show slots.length + remaining ≤ _; omega, rfl⟩
  · exact ⟨by show slots.length + remaining ≤ _; omega, after.2⟩
  · refine ⟨?_, after.2⟩
    show (core.append (own _, slots)).length + remaining ≤ core.slotCap
    rw [append_eq _ _ (by omega), List.length_append, List.length_singleton]; omega
  · refine ⟨?_, rfl, after.2⟩
    show (core.append (_, slots)).length + remaining ≤ core.slotCap
    rw [append_eq _ _ (by omega), List.length_append, List.length_singleton]; omega

include hashOfLaw in
/-- The wrapper's reaction matches entering the inner machine's next state. -/
theorem post_matches (k : core.scalar.Value) (slots : List (Unit ⊕ scalar.Value base)) (room : slots.length < core.slotCap)
    (head : core.forgeryIn.Value ⊕ (Request × A)) (s : witness.machine.State) (after : After caller fuel invariant witness head s)
    (p : (core.output wrapper.outer.good.forgery outLe).valid (core.postFn routines ((k, slots), head))) :
    CallerMachine.Matches (wrapper.machine routines caller finish messageTotal fuel invariant witness) queryOut
      (stateView routines caller wrapper finish messageTotal fuel invariant witness)
      (wrapper.toNext outLe ⟨core.postFn routines ((k, slots), head), p⟩)
      (SynchronizedPS.Wrapped.enter witness.machine (mark routines messageTotal) k s slots) := by
  rcases head with forged | ⟨q, a⟩
  · rw [SynchronizedPS.Wrapped.enter_inl witness.machine (mark routines messageTotal) after]
    refine CallerMachine.Matches.pending (machine := wrapper.machine routines caller finish messageTotal fuel invariant witness)
      (query := queryOut) (state := stateView routines caller wrapper finish messageTotal fuel invariant witness) _ _
      (fun _ => (k, .done forged slots)) ?_
    rw [view_eq]
    show SynchronizedPS.Wrapped.step _ _ _ _ _ (k, .final forged slots) = _
    rw [SynchronizedPS.Wrapped.step_final]
    exact congrArg Sum.inr (sigma_hash_congr (G := G) _ (hashOfLaw ⟨forged.val.1, forged.property.1⟩).symm)
  · obtain ⟨rfl, inner⟩ := after
    obtain ⟨matched, -⟩ := inner
    cases matched with
    | pending _ _ nextIn view =>
      rcases q with n | index | m
      · have henter : SynchronizedPS.Wrapped.enter witness.machine (mark routines messageTotal) k (witness.stateView (.inl n, a)) slots =
            (k, .ready (witness.stateView (.inl n, a)) slots) := by
          rw [SynchronizedPS.Wrapped.enter_inr witness.machine (mark routines messageTotal) view, pendingEvent_random, List.map_nil, List.append_nil]
        rw [henter]
        refine CallerMachine.Matches.pending (machine := wrapper.machine routines caller finish messageTotal fuel invariant witness)
          (query := queryOut) (state := stateView routines caller wrapper finish messageTotal fuel invariant witness) _ _
          (fun r => SynchronizedPS.Wrapped.enter witness.machine (mark routines messageTotal) k (nextIn r) slots) ?_
        rw [view_eq]
        show SynchronizedPS.Wrapped.step _ _ _ _ _ (k, .ready (witness.stateView (.inl n, a)) slots) = _
        rw [SynchronizedPS.Wrapped.step_ready, SynchronizedPS.Wrapped.readyStep_random witness.machine (mark routines messageTotal) finalIndex view]
        rfl
      · have henter : SynchronizedPS.Wrapped.enter witness.machine (mark routines messageTotal) k (witness.stateView (.inr (.inl index), a)) slots =
            (k, .ready (witness.stateView (.inr (.inl index), a)) (core.append (mark routines messageTotal k (.hash index.val), slots))) := by
          rw [SynchronizedPS.Wrapped.enter_inr witness.machine (mark routines messageTotal) view, pendingEvent_hash, List.map_cons, List.map_nil,
            append_eq _ _ room]
        rw [henter]
        refine CallerMachine.Matches.pending (machine := wrapper.machine routines caller finish messageTotal fuel invariant witness)
          (query := queryOut) (state := stateView routines caller wrapper finish messageTotal fuel invariant witness) _ _
          (fun h => SynchronizedPS.Wrapped.enter witness.machine (mark routines messageTotal) k (nextIn h)
            (core.append (mark routines messageTotal k (.hash index.val), slots))) ?_
        rw [view_eq]
        show SynchronizedPS.Wrapped.step _ _ _ _ _ (k, .ready (witness.stateView (.inr (.inl index), a))
          (core.append (mark routines messageTotal k (.hash index.val), slots))) = _
        rw [SynchronizedPS.Wrapped.step_ready, SynchronizedPS.Wrapped.readyStep_hash witness.machine (mark routines messageTotal) finalIndex view]
        rfl
      · have henter : SynchronizedPS.Wrapped.enter witness.machine (mark routines messageTotal) k (witness.stateView (.inr (.inr m), a)) slots =
            (k, .ready (witness.stateView (.inr (.inr m), a)) (core.append (mark routines messageTotal k (.sign m.val), slots))) := by
          rw [SynchronizedPS.Wrapped.enter_inr witness.machine (mark routines messageTotal) view, pendingEvent_sign, List.map_cons, List.map_nil,
            append_eq _ _ room]
        rw [henter]
        refine CallerMachine.Matches.pending (machine := wrapper.machine routines caller finish messageTotal fuel invariant witness)
          (query := queryOut) (state := stateView routines caller wrapper finish messageTotal fuel invariant witness) _ _
          (fun h => (k, .gotHash (witness.stateView (.inr (.inr m), a)) h (core.append (mark routines messageTotal k (.sign m.val), slots)))) ?_
        rw [view_eq]
        show SynchronizedPS.Wrapped.step _ _ _ _ _ (k, .ready (witness.stateView (.inr (.inr m), a))
          (core.append (mark routines messageTotal k (.sign m.val), slots))) = _
        rw [SynchronizedPS.Wrapped.step_ready, SynchronizedPS.Wrapped.readyStep_sign witness.machine (mark routines messageTotal) finalIndex view]
        exact congrArg Sum.inr (sigma_hash_congr (G := G) _ (hashOfLaw m).symm)

/-! ## The records -/

/-- The inner caller's first step is matched by the inner machine's initial state. -/
theorem initial_after (pk : core.inner.key.Value) : After caller fuel invariant witness (caller.initial pk) (witness.machine.init pk.val) := by
  have implements := (implementsWithin_iff_implements_and_bound _ _ _).mp witness.implements
  have valid := invariant.initialValid pk
  generalize hs : witness.machine.init pk.val = s at implements
  have matched := witness.initialMatches pk
  rw [hs] at matched
  rcases hinit : caller.initial pk with forged | ⟨q, a⟩
  · rw [hinit] at matched
    cases matched with
    | returned _ _ view => exact view
  · rw [hinit] at matched valid
    cases matched with
    | pending _ _ next view =>
      exact ⟨rfl, .pending q a next view, witness.source pk.val, fuel, hs ▸ implements.1 pk.val, implements.2 pk.val, valid⟩

variable (fuelOut : Nat) (roomOut : fuelOut + 1 ≤ core.slotCap)
  (innerBounds : Caller.Bounds core.inner.good core.inner.goodSetup caller)
  (finishTime finishWords finishSlots : Nat) (finishBound : finish.BoundedBy finishTime finishWords)
  (finishNames : NamesAccounted finish.program.code finishSlots)
  (reserve : core.slotsAll routines caller innerBounds finishSlots + 3000000 * core.unitW routines caller innerBounds finishWords + 2 < 2 ^ w)

local notation "outerCaller" => wrapper.toCaller routines caller outLe finish callerReserve initialReserve innerBounds finishTime finishWords finishSlots finishBound finishNames reserve

include hashOfLaw fmaLaw roomOut in
/-- The wrapper caller's invariant. -/
def invariant' : Invariant wrapper.outer.good wrapper.outer.goodSetup outerCaller fuelOut where
  domain := domain routines caller wrapper fuel invariant witness
  advanceValid := by
    rintro remaining q ⟨⟨⟨k, slots⟩, a | ⟨m, a⟩ | ⟨⟨m, h⟩, a⟩ | forged⟩, pc⟩ hdom represented original matched
    · obtain ⟨room, hInner⟩ := hdom
      have room' : slots.length + remaining + 1 ≤ core.slotCap := room
      rcases q with n | index | m
      · obtain ⟨nextIn, view, after⟩ := inner_step caller fuel invariant witness (q := .inl n) hInner represented original (in_of_random wrapper n represented original matched)
        exact post_domain routines caller wrapper outLe fuel invariant witness remaining k slots room' _ _ after _
      · obtain ⟨nextIn, view, after⟩ := inner_step caller fuel invariant witness (q := .inr (.inl index)) hInner represented original (in_of_hash wrapper index represented original matched)
        exact post_domain routines caller wrapper outLe fuel invariant witness remaining k slots room' _ _ after _
      · obtain ⟨nextIn, view, after⟩ := inner_step caller fuel invariant witness (q := .inr (.inr m)) hInner represented original (in_of_sign wrapper m represented original matched)
        exact post_domain routines caller wrapper outLe fuel invariant witness remaining k slots room' _ _ after _
    · obtain ⟨room, rfl, hInner⟩ := hdom
      have room' : slots.length + remaining + 1 ≤ core.slotCap := room
      obtain ⟨point, rfl, -⟩ := point_of_hash _ represented original (in_of_hash wrapper _ represented original matched)
      exact ⟨by show slots.length + remaining ≤ _; omega, rfl, hInner⟩
    · obtain ⟨room, rfl, hInner⟩ := hdom
      have room' : slots.length + remaining + 1 ≤ core.slotCap := room
      obtain ⟨σ, rfl, -⟩ := point_of_sign m represented original (in_of_sign wrapper m represented original matched)
      obtain ⟨nextIn, view, after⟩ := inner_step caller fuel invariant witness hInner (.inr (routines.fmaFn (routines.corrFn (k, m), (h, σ))))
        (σ.val + corr routines messageTotal k m.val • h.val) (corrected_matches routines messageTotal fmaLaw k m h σ)
      exact post_domain routines caller wrapper outLe fuel invariant witness remaining k slots room' _ _ after _
    · trivial
  initialValid value :=
    post_domain routines caller wrapper outLe fuel invariant witness fuelOut ⟨value.val.2, value.property.2⟩ [] (by show 0 + fuelOut + 1 ≤ _; omega)
      _ _ (initial_after caller fuel invariant witness ⟨value.val.1, value.property.1⟩) _

/-- The wrapper's source program: the inner source under the wrapper translation. -/
noncomputable def source (u : PK × scalar.Value base) :
    OracleComp (advSpec (key.Value base) (key.Value base × scalar.Value base) G) wrapper.outer.good.forgery.Value :=
  SynchronizedPS.Wrapped.translate finalIndex (fun u m => corr routines messageTotal (proj u) m)
    (fun u result events => wrapper.fin finish (proj u) result (events.map (mark routines messageTotal (proj u)))) u (witness.source u.1) []

variable (signs : Nat) (signQueries : ∀ pk, IsQueryBoundP (witness.source pk) SynchronizedPS.Wrapped.isSign signs)
  (fuelRoom : fuel ≤ core.slotCap) (fuelLe : fuel + signs + 1 ≤ fuelOut)

include signQueries fuelRoom fuelLe in
theorem implements : (wrapper.machine routines caller finish messageTotal fuel invariant witness).ImplementsWithin
    (wrapper.source routines caller finish messageTotal fuel invariant witness) fuelOut := by
  have h := SynchronizedPS.Wrapped.implementsWithin witness.machine Prod.fst proj (corr routines messageTotal) (mark routines messageTotal) finalIndex
    (wrapper.fin finish) (fun u m => corr routines messageTotal (proj u) m)
    (fun u result events => wrapper.fin finish (proj u) result (events.map (mark routines messageTotal (proj u)))) core.slotCap
    (fun _ _ => rfl) (fun _ _ _ _ => rfl) witness.source fuel signs witness.implements signQueries fuelRoom
  rw [implementsWithin_iff_implements_and_bound] at h ⊢
  exact ⟨h.1, fun u => (h.2 u).mono fuelLe⟩

include hashOfLaw fmaLaw roomOut signQueries fuelRoom fuelLe in
/-- The wrapper caller corresponds to the wrapper machine. -/
noncomputable def correspondence : Correspondence wrapper.outer.good wrapper.outer.goodSetup outerCaller fuelOut
    (wrapper.invariant' routines caller outLe finish callerReserve initialReserve messageTotal fmaLaw fuel invariant witness fuelOut roomOut
      innerBounds finishTime finishWords finishSlots finishBound finishNames reserve)
    (Equiv.refl (key.Value base)) where
  source := wrapper.source routines caller finish messageTotal fuel invariant witness
  machine := wrapper.machine routines caller finish messageTotal fuel invariant witness
  implements := wrapper.implements routines caller finish messageTotal fuel invariant witness fuelOut signs signQueries fuelRoom fuelLe
  stateView := stateView routines caller wrapper finish messageTotal fuel invariant witness
  advanceMatches := by
    rintro remaining q ⟨⟨⟨k, slots⟩, a | ⟨m, a⟩ | ⟨⟨m, h⟩, a⟩ | forged⟩, pc⟩ hdom next hview represented original matched
    all_goals obtain ⟨q', hq⟩ : ∃ q' : Request, q' = q := ⟨q, rfl⟩
    all_goals subst hq
    · obtain ⟨room, hInner⟩ := hdom
      have room' : slots.length + remaining + 1 ≤ core.slotCap := room
      have hview' : SynchronizedPS.Wrapped.step witness.machine (corr routines messageTotal) (mark routines messageTotal) finalIndex (wrapper.fin finish)
          (k, .ready (witness.stateView (q', a)) slots) = .inr ⟨queryOut q', next⟩ := by rw [← view_eq]; exact hview
      rcases q' with n | index | m
      · obtain ⟨nextIn, view, after⟩ := inner_step caller fuel invariant witness (q := .inl n) hInner represented original (in_of_random' wrapper n represented original matched)
        rw [SynchronizedPS.Wrapped.step_ready, SynchronizedPS.Wrapped.readyStep_random witness.machine (mark routines messageTotal) finalIndex view] at hview'
        rw [← next_eq wrapper rfl hview']
        exact post_matches routines caller wrapper outLe finish messageTotal hashOfLaw fuel invariant witness k slots (by omega) _ _ after _
      · obtain ⟨nextIn, view, after⟩ := inner_step caller fuel invariant witness (q := .inr (.inl index)) hInner represented original (in_of_hash' wrapper index represented original matched)
        rw [SynchronizedPS.Wrapped.step_ready, SynchronizedPS.Wrapped.readyStep_hash witness.machine (mark routines messageTotal) finalIndex view] at hview'
        rw [← next_eq wrapper rfl hview']
        exact post_matches routines caller wrapper outLe finish messageTotal hashOfLaw fuel invariant witness k slots (by omega) _ _ after _
      · obtain ⟨matched₀, -⟩ := hInner
        cases matched₀ with
        | pending _ _ nextIn view =>
          rw [SynchronizedPS.Wrapped.step_ready, SynchronizedPS.Wrapped.readyStep_sign witness.machine (mark routines messageTotal) finalIndex view] at hview'
          exact absurd (Sigma.mk.inj_iff.mp (Sum.inr.inj hview')).1 (by simp [WeightedCallerHandler.queryIn])
    · obtain ⟨room, rfl, hInner⟩ := hdom
      obtain ⟨matched₀, -⟩ := hInner
      cases matched₀ with
      | pending _ _ nextIn view =>
        have hview' : SynchronizedPS.Wrapped.step witness.machine (corr routines messageTotal) (mark routines messageTotal) finalIndex (wrapper.fin finish)
            (k, .ready (witness.stateView (.inr (.inr m), a)) slots) = .inr ⟨.inl (.inr m.val.1), next⟩ := by
          rw [← view_eq]
          exact hview.trans (congrArg Sum.inr (sigma_hash_congr (G := G) next (hashOfLaw m)))
        rw [SynchronizedPS.Wrapped.step_ready, SynchronizedPS.Wrapped.readyStep_sign witness.machine (mark routines messageTotal) finalIndex view] at hview'
        rw [← next_eq wrapper rfl hview']
        obtain ⟨point, rfl, rfl⟩ := point_of_hash _ represented original (in_of_hash' wrapper _ represented original matched)
        refine CallerMachine.Matches.pending (machine := wrapper.machine routines caller finish messageTotal fuel invariant witness)
          (query := queryOut) (state := stateView routines caller wrapper finish messageTotal fuel invariant witness) _ _
          (fun (σ : G) => SynchronizedPS.Wrapped.enter witness.machine (mark routines messageTotal) k (nextIn (σ + corr routines messageTotal k m.val • point.val)) slots) ?_
        rw [view_eq]
        show SynchronizedPS.Wrapped.step _ _ _ _ _ (k, .gotHash (witness.stateView (.inr (.inr m), a)) point.val slots) = _
        rw [SynchronizedPS.Wrapped.step_gotHash witness.machine (corr routines messageTotal) (mark routines messageTotal) finalIndex (wrapper.fin finish) view]
        rfl
    · obtain ⟨room, rfl, hInner⟩ := hdom
      have room' : slots.length + remaining + 1 ≤ core.slotCap := room
      obtain ⟨σ, rfl, rfl⟩ := point_of_sign m represented original (in_of_sign' wrapper m represented original matched)
      obtain ⟨nextIn, view, after⟩ := inner_step caller fuel invariant witness hInner (.inr (routines.fmaFn (routines.corrFn (k, m), (h, σ))))
        (σ.val + corr routines messageTotal k m.val • h.val) (corrected_matches routines messageTotal fmaLaw k m h σ)
      have hview' : SynchronizedPS.Wrapped.step witness.machine (corr routines messageTotal) (mark routines messageTotal) finalIndex (wrapper.fin finish)
          (k, .gotHash (witness.stateView (.inr (.inr m), a)) h.val slots) = .inr ⟨.inr m.val, next⟩ := by rw [← view_eq]; exact hview
      rw [SynchronizedPS.Wrapped.step_gotHash witness.machine (corr routines messageTotal) (mark routines messageTotal) finalIndex (wrapper.fin finish) view] at hview'
      rw [← next_eq wrapper rfl hview']
      exact post_matches routines caller wrapper outLe finish messageTotal hashOfLaw fuel invariant witness k slots (by omega) _ _ after _
    · obtain ⟨room, rfl⟩ := hdom
      have hview' : SynchronizedPS.Wrapped.step witness.machine (corr routines messageTotal) (mark routines messageTotal) finalIndex (wrapper.fin finish)
          (k, .final forged slots) = .inr ⟨.inl (.inr forged.val.1.1), next⟩ := by
        rw [← view_eq]
        exact hview.trans (congrArg Sum.inr (sigma_hash_congr (G := G) next (hashOfLaw _)))
      rw [SynchronizedPS.Wrapped.step_final] at hview'
      rw [← next_eq wrapper rfl hview']
      refine CallerMachine.Matches.returned (machine := wrapper.machine routines caller finish messageTotal fuel invariant witness)
        (query := queryOut) (state := stateView routines caller wrapper finish messageTotal fuel invariant witness) _ (k, .done forged slots) ?_
      rw [view_eq, SynchronizedPS.Wrapped.step_done]
      exact congrArg Sum.inl (Subtype.ext (fin_of_valid wrapper finish k forged slots pc.1.2))
  initialMatches value := by
    show CallerMachine.Matches (wrapper.machine routines caller finish messageTotal fuel invariant witness) queryOut
      (stateView routines caller wrapper finish messageTotal fuel invariant witness)
      (wrapper.toNext outLe ⟨core.postFn routines ((⟨value.val.2, value.property.2⟩, []), caller.initial ⟨value.val.1, value.property.1⟩), _⟩)
      (SynchronizedPS.Wrapped.enter witness.machine (mark routines messageTotal) (proj value.val) (witness.machine.init value.val.1) [])
    have hp : proj value.val = ⟨value.val.2, value.property.2⟩ := proj_val value
    rw [hp]
    exact post_matches routines caller wrapper outLe finish messageTotal hashOfLaw fuel invariant witness _ [] (by show 0 < _; omega) _ _
      (initial_after caller fuel invariant witness ⟨value.val.1, value.property.1⟩) _

end Wrapper

end Signatures.Runtime.CaliperBackend.SyncWrap
