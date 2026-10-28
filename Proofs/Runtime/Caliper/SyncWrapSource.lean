import Proofs.Runtime.Caliper.SyncWrapCorrespondence
import Proofs.Runtime.Caliper.SyncWrapFinish

/-! The wrapper caller's source program, read as a weighted LazyAGM adversary on keyed inputs
`(pk, k)`, is the synchronized PS wrapper `Wrapped.wrap` of the attacker whose proof view the
inner caller implements. Only the attacker's program at the given key matters to the weighted
list reductions, so the Caliper solvers over the outer caller are the four solvers of
`WrappedSecurity.lean` with the known key drawn from the certified scalar source. -/
namespace Signatures.Runtime.CaliperBackend.SyncWrap
open Caliper BoundedSource WeightedFull OracleComp OracleSpec Model.LazyAGM SynchronizedPS.Wrapped
open PFunctor PFunctor.DynSystem PFunctor.DynSystem.DynComputation

set_option linter.unusedSectionVars false

/-- A single-signer forgery reported with no co-signers. -/
def _root_.SynchronizedPS.Wrapped.embed {F M : Type} (out : Output F M) : Output F (M × List ((F × F) × F)) :=
  ⟨(out.mstar, []), out.β, out.γ, out.ξ⟩

/-- The good list reduction runs the attacker only at the given key. -/
theorem _root_.Model.LazyAGM.WeightedReduction.goodProgram_congr {F ι M G₁ G₂ G₂' : Type} [Field F] [AddCommGroup G₁] [Module F G₁]
    (terms : M → List (ι × F)) (g X : G₁) {pk : G₂} {pk' : G₂'} {A : Adversary F ι M G₁ G₂} {A' : Adversary F ι M G₁ G₂'}
    (same : A.main pk = A'.main pk') :
    WeightedReduction.goodProgram terms g X pk A = WeightedReduction.goodProgram terms g X pk' A' := by
  unfold WeightedReduction.goodProgram WeightedReduction.privateRun
  rw [same]

/-- The bad list reduction runs the attacker only at the given key. -/
theorem _root_.Model.LazyAGM.WeightedReduction.badProgram_congr {F ι M G₁ G₂ G₂' : Type} [Field F] [AddCommGroup G₁] [Module F G₁]
    (terms : M → List (ι × F)) (g X : G₁) {pk : G₂} {pk' : G₂'} (kappa : F) {A : Adversary F ι M G₁ G₂} {A' : Adversary F ι M G₁ G₂'}
    (same : A.main pk = A'.main pk') :
    WeightedReduction.badProgram terms g X pk kappa A = WeightedReduction.badProgram terms g X pk' kappa A' := by
  unfold WeightedReduction.badProgram WeightedReduction.privateRun
  rw [same]

variable {w : Nat} {Atom : Type} {base : Atom → Type} {key scalar : Ty Atom} {G K₀ A : Type}
  [Field (scalar.Value base)] [AddCommGroup G] [Module (scalar.Value base) G] [DecidableEq (key.Value base)]
  [AddCommGroup K₀] [Module (scalar.Value base) K₀]
  {core : Core w (key.Value base) (key.Value base × scalar.Value base) G (scalar.Value base) (K₀ × K₀) A}
  (routines : Routines core) (caller : SharedCaller core.inner)
  (wrapper : Wrapper core) (outLe : wrapper.outer.good.forgery.representation.encoding.words ≤ core.outWords)
  (finRoutines : Wrapper.FinishRoutines core)
  (messageTotal : ∀ m, core.message.valid m)
  (fuel : Nat) (invariant : Invariant core.inner.good core.inner.goodSetup caller fuel)
  (witness : Correspondence core.inner.good core.inner.goodSetup caller fuel invariant (Equiv.refl (key.Value base)))


namespace Wrapper

/-- The slot entries of recorded events are representable. -/
theorem marks_valid (d : core.scalar.Value) (events : List (Event (scalar.Value base) (key.Value base))) (room : events.length ≤ core.slotCap) :
    core.slots.valid (events.map (mark routines messageTotal d)) := by
  refine ⟨by simpa using room, ?_⟩
  intro entry mem
  rw [List.mem_map] at mem
  obtain ⟨event, -, rfl⟩ := mem
  cases event with
  | hash _ => exact trivial
  | sign m => exact (routines.corrFn (d, ⟨m, messageTotal m⟩)).property

/-- The finish's coefficient list over the recorded marks is the wrapper's `remap`. -/
theorem remapMarks_map_mark (d : core.scalar.Value) (γ ξ : List (scalar.Value base)) (events : List (Event (scalar.Value base) (key.Value base))) (i j : Nat) :
    remapMarks γ ξ (events.map (mark routines messageTotal d)) i j = remap (corr routines messageTotal d) γ ξ events i j := by
  induction events generalizing i j with
  | nil => rfl
  | cons event rest ih =>
    cases event with
    | hash _ => exact congrArg _ (ih _ _)
    | sign m => exact congrArg _ (ih _ _)

/-- The wrapper caller's source as a weighted adversary on keyed inputs. -/
noncomputable def outerAdversary : Adversary (scalar.Value base) (key.Value base) (key.Value base × scalar.Value base) G ((K₀ × K₀) × scalar.Value base) where
  main u := (fun answer => WeightedCallerProgram.output answer.val) <$>
    wrapper.source routines caller (wrapper.finish outLe finRoutines) messageTotal fuel invariant witness u

theorem outerAdversary_main (u : (K₀ × K₀) × scalar.Value base) :
    (wrapper.outerAdversary routines caller outLe finRoutines messageTotal fuel invariant witness).main u =
      (fun answer => WeightedCallerProgram.output answer.val) <$>
        wrapper.source routines caller (wrapper.finish outLe finRoutines) messageTotal fuel invariant witness u := rfl

theorem proj_pair (pk : core.inner.key.Value) (s : core.scalar.Value) : proj (core := core) (pk.val, s.val) = s :=
  proj_val (core := core) ⟨(pk.val, s.val), ⟨pk.property, s.property⟩⟩

variable (V : SynchronizedPS.Proofs.View (scalar.Value base) (key.Value base) G K₀)
  (sourceEq : ∀ pk : core.inner.key.Value,
    embed <$> ((fun answer => WeightedCallerProgram.output answer.val) <$> witness.source pk.val) = V.main pk.val)
  (correction : scalar.Value base → key.Value base × scalar.Value base → scalar.Value base)
  (final : scalar.Value base → SynchronizedPS.Forgery (scalar.Value base) (key.Value base) → scalar.Value base) (keys : K₀ → K₀ × K₀)
  (corrLaw : ∀ (d : core.scalar.Value) (m : core.message.Value), (routines.corrFn (d, m)).val = correction d.val m.val)
  (finLaw : ∀ (d : core.scalar.Value) (m : key.Value base × scalar.Value base), finRoutines.negFn (finRoutines.finFn (d.val, m)) = -(final d.val (m, [])))
  (mulLaw : ∀ a b, finRoutines.mulFn (a, b) = a * b)
  (fuelRoom : fuel ≤ core.slotCap)

include sourceEq corrLaw finLaw mulLaw fuelRoom in
/-- **The outer adversary is the wrapped attacker.** At a representable key `pk = keys pk₀` and
representable known key `s`, the outer source is `Wrapped.wrap` around the attacker. -/
theorem outerAdversary_main_eq (pk : core.inner.key.Value) (s : core.scalar.Value) (pk₀ : K₀) (hk : keys pk₀ = pk.val) :
    (wrapper.outerAdversary routines caller outLe finRoutines messageTotal fuel invariant witness).main (pk.val, s.val) =
      (wrap (correction s.val) (final s.val) keys V).main pk₀ := by
  have hproj : proj (core := core) (pk.val, s.val) = s := proj_pair pk s
  have bound := ((implementsWithin_iff_implements_and_bound _ _ _).mp witness.implements).2 pk.val
  have corrFun : corr routines messageTotal s = correction s.val := by
    funext m
    exact corrLaw s ⟨m, messageTotal m⟩
  rw [outerAdversary_main, source, translate_map_out, wrap_main, hk, ← sourceEq pk, Functor.map_map,
    translate_map_in (fun result => result.mstar.1.1) _ _ (fun a => embed (WeightedCallerProgram.output a.val)) finalIndex (fun _ => rfl)]
  symm
  refine translate_congr _ _ _ _ _ pk₀ (pk.val, s.val) ?_ core.slotCap ?_ _ [] fuel bound (by simpa using fuelRoom)
  · intro m
    rw [hproj]
    exact (corrLaw s ⟨m, messageTotal m⟩).symm
  · intro result events room
    rw [hproj, fin_of_valid wrapper (wrapper.finish outLe finRoutines) s result _ (marks_valid routines messageTotal s events room),
      finishFn_eq wrapper finRoutines mulLaw _ (by simpa using room), remapMarks_map_mark, corrFun, finLaw]
    rfl

end Wrapper

end Signatures.Runtime.CaliperBackend.SyncWrap
