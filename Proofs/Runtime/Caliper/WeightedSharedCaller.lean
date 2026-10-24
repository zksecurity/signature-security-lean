import Proofs.Runtime.Caliper.WeightedSharedLayouts

/-! The same local attacker code is used by both weighted reductions. The cache
and configuration are private to the reduction, so changing their layouts does
not require a second attacker implementation or source computation. -/
namespace Signatures.Runtime.CaliperBackend.WeightedFull
open Caliper BoundedSource

structure Caller.Limits where
  step : Budget
  initial : Budget
  slots : Nat

variable {w : Nat} {M G PK A : Type} {Atom : Type} {base : Atom → Type} {key scalar : Ty Atom}
    [Zero (scalar.Value base)] (layout : SharedLayouts w (key.Value base) M G (scalar.Value base) PK A)

abbrev SharedCaller := Caller (base := base) (key := key) (val := scalar) layout.good layout.goodSetup.key.representation

def SharedCaller.bad (caller : SharedCaller layout) :
    Caller (base := base) (key := key) (val := .pair scalar scalar) layout.bad layout.badSetup.key.representation where
  advance := caller.advance
  continuation := caller.continuation
  localNameFits := caller.localNameFits
  initial := caller.initial
  initialCode := caller.initialCode
  initialNameFits := caller.initialNameFits

theorem SharedLayouts.headValid_same {B : Type} (domain : Nat → layout.good.Request × A → Prop)
    (remaining : Nat) (head : B ⊕ (layout.good.Request × A)) :
    WeightedCaller.HeadValid layout.good.service layout.good.randomBound domain remaining head ↔
      WeightedCaller.HeadValid layout.bad.service layout.bad.randomBound domain remaining head := by
  cases head <;> rfl

theorem SharedLayouts.queryIn_same {J : Type} (decode : key.Value base → J) :
    WeightedCallerHandler.queryIn layout.bad.service layout.bad.randomBound decode =
      WeightedCallerHandler.queryIn layout.good.service layout.good.randomBound decode := by
  funext q
  rcases q with n | (index | message) <;> rfl

variable [DecidableEq (key.Value base)] [SampleableType (scalar.Value base)]
    [AddCommMonoid (scalar.Value base)] [SMul (scalar.Value base) (scalar.Value base)]
    (caller : SharedCaller layout) (fuel : Nat)
    (invariant : Invariant (base := base) (key := key) (val := scalar) layout.good layout.goodSetup caller fuel)

def SharedCaller.badInvariant : Invariant (base := base) (key := key) (val := .pair scalar scalar)
    layout.bad layout.badSetup (caller.bad layout) fuel where
  domain := invariant.domain
  advanceValid := by
    intro remaining q c valid represented original matched
    apply (layout.headValid_same invariant.domain remaining (caller.advance (c, represented))).mp
    rcases q with n | (index | message) <;> cases represented <;>
      exact invariant.advanceValid remaining _ c valid _ original matched
  initialValid value := (layout.headValid_same invariant.domain fuel (caller.initial value)).mp (invariant.initialValid value)

variable {J : Type} [DecidableEq J] (keys : J ≃ key.Value base)
    (witness : Correspondence (base := base) (key := key) (val := scalar)
      layout.good layout.goodSetup caller fuel invariant keys)

def SharedCaller.badCorrespondence : Correspondence (base := base) (key := key) (val := .pair scalar scalar)
    layout.bad layout.badSetup (caller.bad layout) fuel (caller.badInvariant layout fuel invariant) keys where
  source := witness.source
  machine := witness.machine
  implements := witness.implements
  stateView := witness.stateView
  advanceMatches := by
    intro remaining q c valid next view represented original matched
    change CallerMachine.Matches witness.machine
      (WeightedCallerHandler.queryIn layout.bad.service layout.bad.randomBound keys.symm)
      witness.stateView (caller.advance (c, represented)) (next original)
    rw [layout.queryIn_same]
    rcases q with n | (index | message) <;> cases represented <;>
      exact witness.advanceMatches remaining _ c valid next view _ original matched
  initialMatches value := by
    change CallerMachine.Matches witness.machine
      (WeightedCallerHandler.queryIn layout.bad.service layout.bad.randomBound keys.symm)
      witness.stateView (caller.initial value) (witness.machine.init value.val)
    rw [layout.queryIn_same]
    exact witness.initialMatches value

omit [SampleableType (scalar.Value base)] [AddCommMonoid (scalar.Value base)] [SMul (scalar.Value base) (scalar.Value base)] [DecidableEq J] in
def SharedCaller.badBounds (bounds : Caller.Bounds (base := base) (key := key) (val := scalar)
    layout.good layout.goodSetup caller) : Caller.Bounds (base := base) (key := key) (val := .pair scalar scalar)
      layout.bad layout.badSetup (caller.bad layout) where
  step := bounds.step
  initial := bounds.initial
  localTime := bounds.localTime
  initialTime := bounds.initialTime
  localWords := bounds.localWords
  initialWords := bounds.initialWords
  slots := bounds.slots
  localNames := bounds.localNames
  initialNames := bounds.initialNames
end Signatures.Runtime.CaliperBackend.WeightedFull
