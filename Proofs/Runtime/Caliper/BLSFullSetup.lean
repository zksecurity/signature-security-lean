import Proofs.Runtime.Caliper.BLSFullProgram

/-! Setup produces the exact represented input consumed by the complete caller.
Empty-store readiness is derived from query/cache capacities, including the
extra private reads required by extraction. -/
namespace Signatures.Runtime.CaliperBackend.BLSFull
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat} {M F G K A : Type} (layout : Layouts w M F G K A)

def goodAdmitted (fuel : Nat) (value : layout.key.Value × layout.good.service.store.Value) : Prop :=
  BLSReply.Reserved layout.good.service fuel value.2.val ∧
    value.2.val.2.1.length + value.2.val.2.2.1.length + value.2.val.2.2.2.length + 2 * fuel + 1 ≤ layout.scheme.cache.capacityPred + 1
def badAdmitted (fuel : Nat) (value : layout.key.Value × layout.bad.service.store.Value) : Prop :=
  BLSReply.Reserved layout.bad.service fuel value.2.val ∧
    value.2.val.2.1.length + value.2.val.2.2.1.length + value.2.val.2.2.2.length + 2 * fuel + 1 ≤ layout.scheme.cache.capacityPred + 1

/-- The caller's local domain follows its pending request and state. Validity
is required only for replies that match that request. -/
structure Caller.Invariant (caller : Caller layout) (fuel : Nat) where
  domain : Nat → layout.Request × A → Prop
  goodAdvance : ∀ remaining q c, domain (remaining + 1) (q, c) →
    ∀ represented original, BLSCallerHandler.replyMatches layout.good.service layout.randomBound q represented original →
      BLSCaller.HeadValid layout.good.service layout.randomBound domain remaining (caller.advance (c, represented))
  badAdvance : ∀ remaining q c, domain (remaining + 1) (q, c) →
    ∀ represented original, BLSCallerHandler.replyMatches layout.bad.service layout.randomBound q represented original →
      BLSCaller.HeadValid layout.bad.service layout.randomBound domain remaining (caller.advance (c, represented))
  initial : ∀ value, BLSCaller.HeadValid layout.good.service layout.randomBound domain fuel (caller.initial value)

theorem good_setup_refines : Interactive.Refines layout.port .unit layout.setup.challenge.representation layout.goodInput
    (fun value => pure (goodStart layout value)) (BLSSetup.goodCode layout.setup) := by
  have viewed := (Interactive.Refines.compute layout.port .unit (BLSSetup.good layout.setup).program).viewOutput
    layout.goodInput layout.goodSetupView layout.good_setup_bytes
  convert viewed using 1 <;> rfl

theorem good_start_admitted (fuel : Nat) (logRoom : fuel ≤ layout.tokens.capacity)
    (cacheRoom : 2 * fuel + 1 ≤ layout.scheme.cache.capacityPred + 1) (value : layout.setup.challenge.Value) :
    goodAdmitted layout fuel (goodStart layout value) := by
  have logs : fuel ≤ layout.scheme.capacityPred + 1 := by
    change fuel ≤ layout.tokens.capacity - 1 + 1
    have positive := layout.shared.positive
    omega
  refine ⟨BLSSetup.good_reserved layout.setup fuel (by change fuel ≤ layout.scheme.cache.capacityPred + 1; omega) logs value, ?_⟩
  change 0 + 0 + 0 + 2 * fuel + 1 ≤ layout.scheme.cache.capacityPred + 1
  omega

variable {Atom : Type} {base : Atom → Type} {key val : Ty Atom}
    [DecidableEq (key.Value base)] [Zero (val.Value base)] [Mul (val.Value base)] [Add (val.Value base)]
    [Sub (val.Value base)] [Neg (val.Value base)] [Div (val.Value base)] [SMul (val.Value base) G] [Add G] [SMul (val.Value base) K]
    (layout : Layouts w (key.Value base) (val.Value base) G K A) (routines : Routines layout)
    (draw : Interactive.Code w) (drawSource : ProbComp layout.scheme.cache.value.Value)
    (drawCorrect : Interactive.Refines layout.port .unit layout.scheme.cache.lookup.unit.representation
      layout.scheme.cache.value.representation (fun _ => drawSource) draw)

omit [DecidableEq (key.Value base)] in
include drawCorrect in
theorem bad_setup_refines : Interactive.Refines layout.port .unit layout.setup.challenge.representation layout.badInput
    (badStart layout routines drawSource)
    (BLSSetup.badCode layout.setup layout.port draw routines.keyScale routines.keyNames.buffers (by have := routines.reserve; omega)) :=
  (BLSSetup.bad_refines layout.setup layout.port draw drawSource drawCorrect routines.keyScale routines.keyNames.buffers (by have := routines.reserve; omega)).viewOutput
    layout.badInput layout.badSetupView layout.bad_setup_bytes

omit [DecidableEq (key.Value base)] in
theorem bad_start_admitted (fuel : Nat) (logRoom : fuel ≤ layout.tokens.capacity)
    (cacheRoom : 2 * fuel + 1 ≤ layout.scheme.cache.capacityPred + 1) (value : layout.setup.challenge.Value)
    (answer : layout.key.Value × layout.bad.service.store.Value) (reached : answer ∈ support (badStart layout routines drawSource value)) :
    badAdmitted layout fuel answer := by
  have logs : fuel ≤ layout.scheme.capacityPred + 1 := by
    change fuel ≤ layout.tokens.capacity - 1 + 1
    have positive := layout.shared.positive
    omega
  unfold badStart at reached
  rw [support_map] at reached
  obtain ⟨initialized, supported, rfl⟩ := reached
  unfold BLSSetup.badSource at supported
  erw [support_map] at supported
  obtain ⟨sampled, _, rfl⟩ := supported
  refine ⟨BLSSetup.bad_reserved layout.setup fuel
    (by change fuel ≤ layout.scheme.cache.capacityPred + 1; omega) logs (BLSSetup.sampledValue layout.setup value sampled), ?_⟩
  change 0 + 0 + 0 + 2 * fuel + 1 ≤ layout.scheme.cache.capacityPred + 1
  omega
end Signatures.Runtime.CaliperBackend.BLSFull
