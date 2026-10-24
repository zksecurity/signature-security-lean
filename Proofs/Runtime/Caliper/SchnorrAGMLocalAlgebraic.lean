import Proofs.Runtime.Caliper.SchnorrAGMPartialCaller

/-! Algebraicity is checked on the caller's local outgoing packets against the
chronological received basis. A source-only fallback with no outgoing groups
is valid at every basis, including unrepresented oracle replies. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Full.Caller.Partial
open Caliper OracleComp OracleSpec AlgebraicGroupModel.Interaction
open Signatures.Runtime.SchnorrAGM.Native
variable {w qH qS randomBound : Nat} {M F G A : Type}
    (layout : CallerExtraction.Layouts w M F G qH qS randomBound A)

/-- Preserve represented data and remove every group output and explanation. -/
def blank (value : layout.forgery.Value) : layout.forgery.Value :=
  ⟨(value.val.1, [], []), value.property.1,
    ⟨Nat.zero_le _, by simp⟩, ⟨Nat.zero_le _, by simp⟩⟩

variable [Zero F] [AddMonoid G] [SMul F G]
theorem blank_valid (value : layout.forgery.Value) (basis : Groups (_root_.Schnorr.AGM.Group G)) :
    (Interface.decodeForgery (blank layout value).val).Valid basis :=
  fun _ => .nil

variable (caller : Caller layout)

/-- Every represented continuation must explain its outgoing groups using the
actual basis extended by the original reply. No separate source tree occurs. -/
def LocallyAlgebraic : Nat → Groups (_root_.Schnorr.AGM.Group G) →
    layout.forgery.Value ⊕ (layout.Request × A) → Prop
  | _, basis, .inl output => (Interface.decodeForgery output.val).Valid basis
  | 0, _, .inr _ => False
  | fuel + 1, basis, .inr (q, state) => (CallerHandler.query layout.service q).Valid basis ∧
      ∀ original represented, CallerHandler.decodeReply layout.service q original = some represented →
        LocallyAlgebraic fuel (extend basis original.groups) (caller.advance (state, represented))

variable (fallback : layout.forgery.Value)
    (fallbackValid : ∀ basis, (Interface.decodeForgery fallback.val).Valid basis)

include fallbackValid in
theorem source_algebraic (fuel : Nat) (basis : Groups (_root_.Schnorr.AGM.Group G))
    (head : layout.forgery.Value ⊕ (layout.Request × A)) (algebraic : LocallyAlgebraic layout caller fuel basis head) :
    IsAlgebraic basis ((fun value => Interface.decodeForgery value.val) <$>
      PartialCaller.source (CallerHandler.query layout.service) (CallerHandler.decodeReply layout.service)
        caller.advance fallback fuel head) := by
  induction fuel generalizing basis head with
  | zero =>
    cases head with
    | inl output => exact algebraic
    | inr pending => exact False.elim algebraic
  | succ fuel ih =>
    cases head with
    | inl output => exact algebraic
    | inr pending =>
      change (CallerHandler.query layout.service pending.1).Valid basis ∧
        ∀ original, IsAlgebraic (extend basis original.groups)
          ((fun value => Interface.decodeForgery value.val) <$>
            PartialCaller.source (CallerHandler.query layout.service) (CallerHandler.decodeReply layout.service)
              caller.advance fallback fuel
                (PartialCaller.next (CallerHandler.query layout.service) (CallerHandler.decodeReply layout.service)
                  caller.advance fallback pending.1 pending.2 original))
      refine ⟨algebraic.1, ?_⟩
      intro original
      cases decoded : CallerHandler.decodeReply layout.service pending.1 original with
      | none =>
        simp only [PartialCaller.next, decoded]
        cases fuel <;> exact fallbackValid _
      | some represented =>
        simp only [PartialCaller.next, decoded]
        exact ih _ _ (algebraic.2 original represented decoded)

end Signatures.Runtime.CaliperBackend.SchnorrAGM.Full.Caller.Partial
